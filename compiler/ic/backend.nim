import # compiler imports

  ".." / [

    ast, cgendata, sighashes, options, modulegraphs, ropes, pathutils,
    ccgutils, extccomp, ndi, msgs, btrees, nversion, condsyms, lineinfos,
    incremental, idgen, idents, magicsys, astalgo, options,
    treetab

  ]

import # stdlib imports

  std / [ db_sqlite, macros, strutils, intsets, tables, sets, sequtils ]

import # ic imports

  spec, frontend, store, utils

type
  ModuleOrProc = BModule or BProc

template db(): DbConn = g.incr.db
template config(): ConfigRef = cache.modules.config

template isSealed*(m: BModule): bool {.dirty.} = false

using
  cache: CacheUnit
  g: ModuleGraph

template rejected*(cache): bool =
  {CacheStrategy.Reads, CacheStrategy.Writes} * cache.strategy == {}

proc mangle*(m: ModuleOrProc; s: PSym): string
proc setLocationRope*(m: BModule; p: PSym or PType; r: Rope)

template readable*(cache): bool = CacheStrategy.Reads in cache.strategy
template writable*(cache): bool = CacheStrategy.Writes in cache.strategy

proc newCacheUnit*[T: CacheableObject](modules: BModuleList; origin: BModule;
                  node: var T; strategy: set[CacheStrategy]): CacheUnit[T]

proc `$`*(cache: CacheUnit[PNode]): string =
  result = $cache.node.kind
  result = "cacheN($#, $#)" % [ result, $cache.strategy ]

proc `$`*(cache: CacheUnit[PSym]): string =
  result = cache.node.name.s
  var
    owner = cache.node.owner
  while owner != nil and owner.owner != nil:
    owner = owner.owner
  if owner != nil and owner.name != nil:
    result &= ".." & $owner.name.s
  result = "cacheS($#, $#)" % [ result, $cache.strategy ]

proc `$`*(cache: CacheUnit[PType]): string =
  result = $cache.node.kind & "-" & $cache.node.uniqueId
  if cache.node.sym != nil:
    result &= "/" & $cache.node.sym.name.s
  result = "cacheT($#, $#)" % [ result, $cache.strategy ]

proc reject(cache: var CacheUnit; value = true) =
  if value:
    if Immutable in cache.strategy and (cache.readable or cache.writable):
      raise newException(Defect, "you want to reject " & $cache)
    if cache.state == Load:
      cache.state = Generate

proc reject*(cache: var CacheUnit; flags: set[CacheStrategy]) =
  cache.strategy.excl flags
  cache.reject true

proc assignStrategy(strategy: var set[CacheStrategy]; node: PSym) =
  ## true if the logic did not change the cacheability of the cache unit
  # not a toplevel proc?
  if node.owner == nil or node.owner.kind != skModule:
    strategy.excl {Reads, Writes}
    strategy.incl Immutable
  # compiler proc that isn't at top level
  elif sfCompilerProc in node.flags and node.owner != nil:
    strategy.excl {Reads, Writes}
    strategy.incl Immutable
  elif lfImportCompilerProc in node.loc.flags:
    strategy.excl {Reads, Writes}
    strategy.incl Immutable

proc assignStrategy(strategy: var set[CacheStrategy]; node: PNode) =
  case node.kind
  of nkSym, nkType:
    discard "we don't know how to cache PNodes that aren't sym | type"
  else:
    strategy.excl {Reads, Writes}
    strategy.incl Immutable

proc shouldAppendModuleName(s: PSym): bool =
  ## are we going to apply top-level mangling semantics?
  const
    never = {sfSystemModule, sfCompilerProc, sfImportc, sfExportc}
  # FIXME: put sfExported into never?
  case s.kind
  of skLocalVars + {skModule, skPackage, skTemp, skParam}:
    result = false
  else:
    if never * s.flags != {}:
      # the symbol uses a name that must not change
      return
    elif s.owner == nil or s.owner.kind in {skModule, skPackage}:
      # the symbol is top-level; add the module name
      result = true
    elif s.kind in routineKinds:
      if s.typ != nil:

        # this minor hack is necessary to make tests/collections/thashes
        # compile. The inlined hash function's original module is
        # ambiguous so we end up generating duplicate names otherwise:

        if s.typ.callConv == ccInline:
          result = true

    # exports get their source module appended
    if sfExported in s.flags:
      result = true

const
  irrelevantForBackend* = {tyGenericBody, tyGenericInst, tyOwned,
                           tyGenericInvocation, tyDistinct, tyRange,
                           tyStatic, tyAlias, tySink, tyInferred}

proc shortKind(k: TTypeKind): string =
  # tell me about it.
  result = $k
  result = result[2 .. min(4, result.high)].toLowerAscii

proc typeName(m: ModuleOrProc; typ: PType; shorten = false): string =
  var typ = typ.skipTypes(irrelevantForBackend)
  case typ.kind
  of tySet, tySequence, tyTypeDesc, tyArray:
    result = shortKind(typ.kind)
    result.add "_"
    result.add typeName(m, typ.lastSon, shorten = shorten)
  of tyVar, tyRef, tyPtr:
    # omit this verbosity for now
    result = typeName(m, typ.lastSon, shorten = shorten)
  else:
    if typ.sym == nil: # or typ.kind notin {tyObject, tyEnum}:
      result = shortKind(typ.kind) & "_" & $typ.uniqueId
    elif shorten:
      result = mangle(typ.sym.name.s)
    else:
      result = mangle(m, typ.sym)

template maybeAppendCounter(result: typed; count: int) =
  if count > 0:
    result.add "_"
    result.add $count

proc getOrSet(conflicts: ConflictsTable; name: string; id: int): int

proc getTypeName(m: BModule; typ: PType): Rope =
  block found:
    # XXX: is this safe (enough)?
    #if typ.loc.r != nil:
    #  break

    # try to find the actual type
    var t = typ
    while t != nil:
      # settle for a symbol if we can find one
      if t.sym != nil:
        if {sfImportc, sfExportc} * t.sym.flags != {}:
          result =
            if t.sym.loc.r != nil:
              # use an existing name if previously mangled
              t.sym.loc.r
            else:
              # else mangle up a new name
              mangle(m, t.sym).rope
          break found
      if t.kind notin irrelevantForBackend:
        # this looks like a good place to stop
        break
      # continue into more precise types
      t = t.lastSon

    assert t != nil
    result =
      if t.loc.r == nil:
        # create one using the closest type
        typeName(m, t).rope
      else:
        # use the closest type which already has a name
        t.loc.r

  if result == nil:
    internalError(m.config, "getTypeName: " & $typ.kind)
  let counter = m.sigConflicts.getOrSet($result, typ.uniqueId)
  result.maybeAppendCounter counter
  m.setLocationRope typ, result

proc getTypeName*(m: BModule; typ: PType; sig: SigHash): Rope =
  result = getTypeName(m, typ)

proc maybeAppendProcArgument(m: ModuleOrProc; s: PSym; nom: var string): bool =
  ## should we add the first argument's type to the mangle?
  assert s.kind in routineKinds
  assert s.typ != nil
  if s.typ.sons.len > 1:
    nom.add "_"
    nom.add typeName(m, s.typ.sons[1], shorten = true)
    result = true

proc mangle*(m: ModuleOrProc; s: PSym): string =
  # TODO: until we have a new backend ast, all mangles have to be done
  # identically

  # start off by using a name that doesn't suck
  result = mangle(s.name.s)

  # add the first argument to procs if possible
  if s.kind in routineKinds and s.typ != nil:
    discard maybeAppendProcArgument(m, s, result)

  # add the module name if necessary, or if it helps avoid a clash
  if s.shouldAppendModuleName or s.name.isNimOrCKeyword:
    let parent = getModule(s)
    if parent != nil:
      result.add "_"
      result.add mangle(parent.name.s)

  # something like `default` might need this check
  if (unlikely) result in m.config.cppDefines:
    result.add "_"
    result.add $s.id

  # FIXME: IC TODO
  {.warning: "confirm that the module id matches the symbol's module".}
  #if getModule(s).id.abs != m.module.id.abs:
  # XXX: we don't do anything special with regard to m.hcrOn (Hot Code Reload)
  assert result.len > 0

proc getSetConflictFromCache(m: BModule; s: PSym; create = true): string =
  template g(): ModuleGraph = m.g.graph
  assert m.sigConflicts != nil
  var counter: int
  var sigstring: string
  let sid = $s.id

  # maybe we'll get out of here trivially...
  result = m.mangle(s)
  if sid in m.sigConflicts:
    return

  const
    query = sql"""
      select id from conflicts
      where nimid = ?
      order by id desc
      limit 1
    """
    insert = sql"""
      insert into conflicts (nimid, signature, name)
      values (?, ?, ?)
    """
  let
    id = db.getValue(query, s.id)
  if id == "":
    if not create:
      assert false, "missing id for " & result & " and no create option"
    # set the counter to the row id, not the symbol id or the actual count
    counter = db.insertID(insert, s.id, sigstring, result).int
  else:
    counter = id.parseInt
  assert counter > 0
  m.sigConflicts[sid] = counter

proc getOrSet(conflicts: ConflictsTable; name: string; id: int): int =
  ## set the counter to indicate the number of collisions at the time the
  ## name was added to the conflicts table.  requires a unique id for the
  ## symbol being added to the table.  returns true if this is the
  ## first instance of the name to enter the table.
  let sid = $id
  result = conflicts.getOrDefault(sid, -1)
  if result == -1:
    result = conflicts.getOrDefault(name, -1)
    if result == -1:
      # start counting at zero so we can omit an initial append
      result = 0
      # set the value for the name indicate the NEXT available counter
      conflicts[name] = 1
    else:
      # set the value for the name indicate the NEXT available counter
      inc conflicts[name]
    conflicts[sid] = result

proc getSetConflict(p: ModuleOrProc; s: PSym;
                     create = true): tuple[name: string; counter: int] =
  ## take a backend module or a procedure being generated and produce an
  ## appropriate name and the instances of its occurence, which may be
  ## incremented for this instance
  template m(): BModule =
    when p is BModule:
      p
    else:
      p.module
  template g(): ModuleGraph = m.g.graph
  var counter: int
  var name: string

  block:
    when p is BModule:
      if g.config.symbolFiles != disabledSf:

        # we can use the IC cache to determine the right name and counter
        # for this symbol

        when false:
          name = m.getSetConflictFromCache(s, create = create)
          assert false, "this code needs work"
          break

    name = mangle(p, s)

  counter = p.sigConflicts.getOrSet(name, s.id)
  if counter == 0:
    # it's the first instance using this name
    if not create:
      debug s
      assert false, "cannot find existing name for: " & name
  result = (name: name, counter: counter)
  # FIXME: add a pass to warm up the conflicts cache

proc idOrSig*(m: ModuleOrProc; s: PSym): Rope =
  ## produce a unique identity-or-signature for the given module and symbol
  let conflict = m.getSetConflict(s, create = true)
  result = conflict.name.rope
  result.maybeAppendCounter conflict.counter

template tempNameForLabel*(m: BModule; label: int): string =
  ## create an appropriate temporary name for the given label
  m.tmpBase & $label & "_"

proc hasTempName*(m: BModule; n: PNode): bool =
  ## true if the module/proc has a temporary cached for the given node
  result = nodeTableGet(m.dataCache, n) != low(int)

proc getTempNameImpl(m: BModule; id: int): string =
  ## the only way to create a new temporary name in a given module
  assert id == m.labels
  # it's a new temporary; increment our counter
  inc m.labels
  # get the appropriate name
  result = m.tempNameForLabel(id)
  # make sure it's not in the conflicts table
  assert result notin m.sigConflicts
  # make sure it's in the conflicts table with the NEXT available counter
  m.sigConflicts[result] = 1

proc getTempName*(m: BModule; n: PNode; r: var Rope): bool =
  ## create or retrieve a temporary name for the given node; returns
  ## true if a new name was created and false otherwise.  appends the
  ## name to the given rope.
  let id = nodeTableTestOrSet(m.dataCache, n, m.labels)
  var name: string
  if id == m.labels:
    name = m.getTempNameImpl(id)
    result = true
  else:
    name = m.tempNameForLabel(id)
    # make sure it's not in the conflicts table under a different id
    assert m.sigConflicts.getOrDefault(name, 1) == 1
    # make sure it's in the conflicts table with the NEXT available counter
    m.sigConflicts[name] = 1

  # add or append it to the result
  if r == nil:
    r = name.rope
  else:
    r.add name

proc getTempName*(m: BModule; n: PNode): Rope =
  ## a simpler getTempName that doesn't care where the name comes from
  discard m.getTempName(n, result)

proc getTempName*(m: BModule): Rope =
  ## a factory for making temporary names for use in the backend; this mutates
  ## the module from which the name originates; this always creates a new name
  result = m.getTempNameImpl(m.labels).rope

proc immutant(flags: var set[CacheStrategy];
              add: set[CacheStrategy] = {};
              del: set[CacheStrategy] = {}) =
  ## mutate a flag set, adding flags only if the set is NOT immutable
  if Immutable notin flags:
    flags.incl add
  flags.excl del
  flags.incl Immutable

proc assignStrategy[T](config: ConfigRef; node: T): set[CacheStrategy] =
  ## figure out whether we are in a position to cache the node and
  ## return a set of flags to indicate such
  when defined(release):
    result.immutant {}
  else:
    # run an assignStrategy appropriate to the node type
    result.assignStrategy node
    # now perhaps mutate the strategy according to compilation options
    case config.symbolFiles
    of disabledSf:
      result.immutant(del = {Reads, Writes})
    of readOnlySf:
      result.immutant(add = {Reads}, del = {Writes})
    of writeOnlySf:
      result.immutant(add = {Writes}, del = {Reads})
    of v2Sf:
      result.immutant(add = {Reads, Writes})

proc rawNewModule*(g: BModuleList; module: PSym; filename: AbsoluteFile): BModule =
  new(result)
  result.g = g
  {.warning: "need this for IC to work!".}
  #result.tmpBase = rope("TM" & $hashOwner(module) & "_")
  result.tmpBase = "T_"
  result.headerFiles = @[]
  result.cfilename = filename
  result.filename = filename
  result.module = module

  # XXX: keep an eye on these:
  result.declaredThings = initIntSet()
  result.declaredProtos = initIntSet()
  initNodeTable(result.dataCache)
  result.typeStack = @[]
  result.initProc = newProc(nil, result)
  result.initProc.options = initProcOptions(result)
  result.preInitProc = newPreInitProc(result)
  #
  # XXX: these, we share currently
  result.typeCache = newTable[SigHash, Rope]()
  result.forwTypeCache = newTable[SigHash, Rope]()
  result.typeInfoMarker = newTable[SigHash, Rope]()
  result.sigConflicts = newTable[string, int]()

  #
  result.typeNodesName = getTempName(result)
  result.nimTypesName = getTempName(result)
  # XXX: end

  # no line tracing for the init sections of the system module so that we
  # don't generate a TFrame which can confuse the stack bottom initialization:
  if sfSystemModule in module.flags:
    incl result.flags, preventStackTrace
    excl(result.preInitProc.options, optStackTrace)

  # XXX: we might need to move these to a non-raw init
  let ndiName = if optCDebug in g.config.globalOptions:
    changeFileExt(completeCfilePath(g.config, filename), "ndi")
  else:
    AbsoluteFile""
  open(result.ndi, ndiName, g.config)

proc rawNewModule*(g: BModuleList; module: PSym; conf: ConfigRef): BModule =
  result = rawNewModule(g, module,
                        AbsoluteFile toFullPath(conf, module.position.FileIndex))

proc createFakeGraph[T: PNode | PSym](modules: BModuleList;
                                      node: T): BModuleList =
  result = newModuleList(modules.graph)
  assert result.modules.len == 0
  let sig = node.sigHash
  for m in modules.modules.items:
    if m == nil:
      result.modules.add nil
    else:
      var
        fake = rawNewModule(result, m.module, m.filename)

      # shared refs
      # XXX: throw this away
      assert m.sigConflicts != nil
      fake.sigConflicts = m.sigConflicts
      fake.typeCache = m.typeCache
      fake.forwTypeCache = m.forwTypeCache
      fake.typeInfoMarker = m.typeInfoMarker
      fake.tmpBase = "T_" & $sig & "_"

      fake.typeNodes = m.typeNodes
      fake.nimTypes = m.nimTypes
      fake.headerFiles = m.headerFiles
      for pair in m.dataCache.data.items:
        if pair.key != nil:
          nodeTablePut(fake.dataCache, pair.key, pair.val)

      fake.flags = m.flags
      fake.declaredThings = m.declaredThings
      fake.declaredProtos = m.declaredProtos

      # these may get reset if they are nil
      fake.initProc = m.initProc
      fake.preInitProc = m.preInitProc

      for ptype in m.typeStack:
        pushType(fake, ptype)

      # make sure our fake module matches the original module
      #when not defined(release):
      #  assert fake.hash == m.hash, "bad hash " & $m.filename

      # these mutate the fake module with new Labels transforms
      fake.typeNodesName = getTempName(fake)
      fake.nimTypesName = getTempName(fake)
      # reset the label counter; the names are different enough
      # and we don't want gratuitous +2 label increments
      fake.labels = m.labels

      fake.injectStmt = m.injectStmt

      if m.initProc.prc == nil:
        fake.initProc = newProc(nil, fake)
      if m.preInitProc.prc == nil:
        fake.preInitProc = newPreInitProc(fake)

      result.modules.add fake
#
# NOTE:
# the origin is the first psym from which we can reach a parent module
#
template origin*(p: var PSym): var PSym = p
template origin*(p: var PType): var PSym = p.sym
proc origin*(p: var PNode): var PSym =
  assert p != nil
  case p.kind
  of nkSym:
    assert p.sym != nil
    result = p.sym.origin
  of nkType:
    assert p.typ != nil
    result = p.typ.origin
  else:
    debug p
    raise

proc origin*(p: PNode): PSym =
  var
    p = p
  result = p.origin

proc findModule*(list: BModuleList; start: PSym): BModule =
  let
    parent = getModule(start)
  assert parent != nil
  block found:
    for m in list.modules.items:
      if m != nil:
        if m.module != nil and m.module.id == parent.id:
          result = m
          break found
    raise newException(Defect, "unable to find module " & $parent.id)

proc findModule*(list: BModuleList; child: BModule): BModule =
  result = findModule(list, child.module)

proc findTargetModule*(cache; child: PNode): BModule =
  ## return a fake module if caching is enabled; else the original module
  if cache.rejected:
    result = cache.origin
  else:
    result = findModule(cache.modules, cache.origin)

proc findTargetModule*(cache; child: BModule): BModule =
  ## return a fake module if caching is enabled; else the original module
  if cache.rejected:
    result = cache.origin
  else:
    result = findModule(cache.modules, child.module)

proc findTargetModule*(cache; child: PSym | PType): BModule =
  ## return a fake module if caching is enabled; else the original module
  if cache.rejected:
    result = cache.origin
  else:
    result = findModule(cache.modules, child.origin)

when false:
  proc pointToModuleIn(p: ptr PSym; modules: BModuleList) =
    {.warning: "this probably doesn't work".}
    if p != nil:
      if p.kind == skModule:
        p[] = findModule(modules, p[]).module
      else:
        pointToModuleIn(addr p[].owner, modules)

  proc pointToModuleIn(p: var CacheableObject; modules: BModuleList) =
    when true:
      when p isnot PNode:
        pointToModuleIn(addr p.origin, modules)
    else:
      {.warning: "this is not even enabled".}

proc encodeTransform(t: Transform): EncodingString =
  template g(): ModuleGraph = t.module.g.graph
  case t.kind
  of Unknown:
    raise newException(Defect, "don't encode unknown transforms")
  of HeaderFile:
    {.warning: "assert no newlines in filenames?".}
    result = t.filenames.join("\n")
  of ThingSet, ProtoSet:
    result = mapIt(t.diff, $it).join("\n")
  of FlagSet:
    result = mapIt(t.flags, $it).join("\n")
  of Injection:
    result = $t.rope
  of GraphRope:
    result = $t.grope
  of TypeStack:
    result = mapIt(t.stack, $it.uniqueId).join("\n")
  of InitProc, PreInit:
    result = $t.prc.id
  of Labels:
    result = $t.labels
  of SetLoc:
    encodeLoc(t.module.g.graph, t.loc, result)
    result = $ord(t.nkind) & "\n" & $t.id & "\n" & $result
  of LiteralData:
    encodeNode(g, t.module.module.info, t.node, result)
    result = $t.val & "\n" & $result

proc storeTransform*[T](cache: var CacheUnit[T]; node: T;
                        transform: Transform) =
  let
    sig = sigHash(node)
  # we add all transforms
  cache.transforms.add sig, transform
  if cache.writable:
    # but we only write to the db if the writable flag is set
    template g(): ModuleGraph = cache.graph
    const
      insertion = sql"""
        insert into transforms (signature, module, kind, data)
        values (?, ?, ?, ?)
      """
    let
      mid = if transform.module == nil: 0 else: transform.module.module.id
    db.exec(insertion, $sig, mid, transform.kind, encodeTransform(transform))

template storeIdSets(cache;
                     parent: BModule; child: BModule;
                     k: TransformKind; name: untyped) =
  if parent.name.len != child.name.len:
    assert len(parent.name - child.name) == 0
    var
      transform: Transform
    case k
    of TransformKind.ProtoSet:
      transform = Transform(kind: TransformKind.ProtoSet, module: parent)
    of TransformKind.ThingSet:
      transform = Transform(kind: TransformKind.ThingSet, module: parent)
    else:
      raise newException(Defect, "bad kind")
    transform.diff = child.name - parent.name
    when not defined(release):
      echo "\tfresh: ", k, " ", transform.diff
    #parent.name = parent.name + child.name
    storeTransform(cache, cache.node, transform)

# the snippet's module is not necessarily the same as the symbol!
proc newSnippet*[T](node: T; module: BModule; sect: TCFileSection): Snippet =
  result = Snippet(signature: node.sigHash, module: module, section: sect)

proc writable*(cache: var CacheUnit; value: bool): bool =
  if Immutable notin cache.strategy:
    if value:
      cache.strategy.incl Writes
    else:
      cache.strategy.excl Writes
  result = cache.writable

proc readable*(cache: var CacheUnit; value: bool): bool =
  if Immutable notin cache.strategy:
    if value:
      cache.strategy.incl Reads
    else:
      cache.strategy.excl Reads
  result = cache.readable

template storeHeaders(cache; parent: BModule; child: BModule) =
  # nil-separated list?
  var
    transform = Transform(kind: HeaderFile, module: parent)
  for filename in child.headerFiles:
    if filename notin parent.headerFiles:
      transform.filenames.add filename
  if transform.filenames.len > 0:
    storeTransform(cache, cache.node, transform)

proc anusedtablemrgeproc(cache;
                          parent: var BModule; child: BModule)
  {.deprecated.} =
  # ❌we are sharing these (for now!)
  ## [SHARE?] sigs -> ropes

  # copy the types over
  for signature, rope in child.typeCache.pairs:
    if signature notin parent.typeCache:
      parent.typeCache[signature] = rope
    when not defined(release):
      echo "typecache size: ", child.typeCache.len
      # XXX

  ## [SHARE?] sigs -> ropes

  # copy the forwarded types over
  for signature, rope in child.forwTypeCache.pairs:
    if signature notin parent.forwTypeCache:
      parent.forwTypeCache[signature] = rope
    when not defined(release):
      echo "forwTypeCache size: ", child.forwTypeCache.len
      # XXX

  ## [SHARE?] sigs -> ropes

  # copy the type info markers over
  for signature, rope in child.typeInfoMarker.pairs:
    if signature notin parent.typeInfoMarker:
      parent.typeInfoMarker[signature] = rope
    when not defined(release):
      echo "typeinfomarker size: ", child.typeInfoMarker.len
      # XXX

proc storeLabels(cache: var CacheUnit; parent: BModule; child: BModule) =
  # copy the labels over
  var
    transform = Transform(kind: Labels, module: parent)
  transform.labels = child.labels - parent.labels
  if transform.labels > 0:
    storeTransform(cache, cache.node, transform)

proc storeTypeStack(cache: var CacheUnit; parent: BModule; child: BModule) =
  # copy the types over
  var
    transform = Transform(kind: TypeStack, module: parent)
  for ptype in child.typeStack:
    transform.stack.add ptype
  if transform.stack.len > 0:
    storeTransform(cache, cache.node, transform)

template storeImpl(cache: var CacheUnit;
                   orig: BModule; body: untyped): untyped =
  assert cache.writable, "attempt to write unwritable cache"

  when not defined(release):
    echo "store for ", cache, " ", orig

  body

  # TODO: if we wrote the cache, we can read it (???)
  #discard cache.readable(true)

macro storeRopes(cache; parent: BModuleList; child: untyped): untyped =
  expectKind child, nnkDotExpr
  let
    field = newStrLitNode($child[1])
    parent = newDotExpr(parent, child[1])  # 2nd half of dot expr
    #graph = newDotExpr(cache, ident"graph")
    node = newDotExpr(cache, ident"node")
  result = quote do:
    if `child` != nil:
      let
        transform = Transform(kind: TransformKind.GraphRope,
                              field: `field`, grope: `child`)
      storeTransform(cache, `node`, transform)

macro storeRope(cache; parent: BModule; child: untyped): untyped =
  expectKind child, nnkDotExpr
  let
    field = newStrLitNode($child[1])
    parent = newDotExpr(parent, child[1])  # 2nd half of dot expr
    #graph = newDotExpr(cache, ident"graph")
    node = newDotExpr(cache, ident"node")
  result = quote do:
    if `child` != nil:
      let
        transform = Transform(kind: TransformKind.Injection,
                              rope: `child`)
      storeTransform(cache, `node`, transform)

macro storeProc(cache; k: TransformKind, parent: BModule;
                child: untyped): untyped =
  expectKind child, nnkDotExpr
  let
    field = newStrLitNode($child[1])
    parent = newDotExpr(parent, child[1])  # 2nd half of dot expr
    #graph = newDotExpr(cache, ident"graph")
    node = newDotExpr(cache, ident"node")
  result = quote do:
    if `child` != nil and `child`.prc != nil:
      if `parent` != nil and `parent`.prc != nil:
        raise newException(Defect, "attempt to replace parent proc")
      let
        transform = Transform(kind: `k`, prc: `child`.prc)
      storeTransform(cache, `node`, transform)

template mergeRope(parent: var Rope; child: Rope): untyped =
  if parent == nil:
    parent = child
  else:
    parent.add child

proc apply(parents: BModuleList; transform: Transform) =
  assert transform.module != nil, "do not use to apply graph-based transforms"
  var
    parent = findModule(parents, transform.module)
  when not defined(release):
    echo "\t", transform.kind, "\t", transform.module
  # we're loading the snippets into fake modules...
  case transform.kind
  of Unknown:
    raise newException(Defect, "attempt to apply unknown transform")
  of HeaderFile:
    for filename in transform.filenames:
      if filename notin parent.headerFiles:
        parent.headerFiles.add filename
  of ThingSet:
    parent.declaredThings = parent.declaredThings.union(transform.diff)
  of ProtoSet:
    parent.declaredProtos = parent.declaredProtos.union(transform.diff)
  of FlagSet:
    parent.flags = parent.flags + transform.flags
  of Injection:
    if parent.injectStmt == nil:
      parent.injectStmt = transform.rope
    else:
      parent.injectStmt.add transform.rope
  of GraphRope:
    case transform.field:
    of "mainModProcs":
      parents.mainModProcs.mergeRope(transform.grope)
    of "mainModInit":
      parents.mainModInit.mergeRope(transform.grope)
    of "otherModsInit":
      parents.otherModsInit.mergeRope(transform.grope)
    of "mainDatInit":
      parents.mainDatInit.mergeRope(transform.grope)
    of "mapping":
      parents.mapping.mergeRope(transform.grope)
    else:
      raise newException(Defect,
                         "unrecognized field: " & transform.field)
  of TypeStack:
    for ptype in transform.stack:
      pushType(parent, ptype)
  of InitProc:
    if parent.initProc != nil and parent.initProc.prc != nil:
      raise newException(Defect, "clashing initProc")
    parent.initProc = newProc(transform.prc, transform.module)
    assert parent.initProc != nil
    assert parent.initProc.prc != nil
  of PreInit:
    if parent.preInitProc != nil and parent.preInitProc.prc != nil:
      raise newException(Defect, "clashing preInitProc")
    parent.preInitProc = newProc(transform.prc, transform.module)
  of Labels:
    parent.labels.inc transform.labels
  of SetLoc:
    case transform.nkind
    of nkSym:
      if symbolAlreadyStored(parents.graph, transform.id):
        raise newException(Defect, "attempt to rewrite nksym")
      #cache.tree.setSymbolLocation(transform.id, transform.loc)
    of nkType:
      if typeAlreadyStored(parents.graph, transform.id):
        raise newException(Defect, "attempt to rewrite nktype")
      #cache.tree.setTypeLocation(transform.id, transform.loc)
    else:
      raise newException(Defect, "unknown kind of location: " & $transform.nkind)
  of LiteralData:
    nodeTablePut(parent.dataCache, transform.node, transform.val)

  when not defined(release):
    echo "\t" & $transform

proc decodeTransform(kind: string; module: BModule;
                     data: string): Transform =
  result = Transform(kind: parseEnum[TransformKind](kind), module: module)
  case result.kind:
  of Unknown:
    raise newException(Defect, "unknown transform in the db")
  of HeaderFile:
    result.filenames = data.split('\n')
  of ThingSet, ProtoSet:
    for value in mapIt(data.split('\n'), parseInt(it)):
      result.diff.incl value
  of FlagSet:
    for value in mapIt(data.split('\n'), parseEnum[CodegenFlag](it)):
      result.flags.incl value
  of Injection:
    result.rope = rope(data)
  of GraphRope:
    let
      splat = data.split('\n', maxsplit = 1)
    result.field = splat[0]
    result.grope = rope(splat[1])
  of TypeStack:
    for value in mapIt(data.split('\n'), parseInt(it)):
      result.stack.add loadType(module.g.graph, value, unknownLineInfo)
  of InitProc, PreInit:
    result.prc = loadSym(module.g.graph, data.parseInt, unknownLineInfo)
  of Labels:
    result.labels = parseInt(data)
  of SetLoc:
    let
      splat = data.split('\n', maxsplit = 2)
    for i, data in splat.pairs:
      case i
      of 0:
        result.nkind = parseInt(data).TNodeKind
      of 1:
        result.id = parseInt(data)
      of 2:
        var b = newBlobReader(data)
        decodeLoc(module.g.graph, b, result.loc, unknownLineInfo)
      else:
        raise
  of LiteralData:
    let
      splat = data.split('\n', maxsplit = 1)
    result.val = splat[0].parseInt
    var
      b = newBlobReader(splat[1])
    result.node = decodeNode(module.g.graph, b, unknownLineInfo)

iterator loadTransforms*(g: ModuleGraph;
                         modules: BModuleList; p: PNode): Transform =
  const
    selection = sql"""
      select kind, module, data
      from transforms
      where signature = ? and module = ?
    """
  let
    name = $p.sigHash
  for row in db.fastRows(selection, name, getModule(p.origin).id):
    # search for the transforms for the given symbol
    let
      mid = row[1].parseInt
    var
      module: BModule
    if mid != 0:
      block found:
        # the modules in the modules list are in the modules list
        for m in modules.modules.items:
          # the module id is in the module's module field
          if m.module.id == mid:
            module = m
            break found
        # we didn't find the matching backend module; for now we throw
        raise newException(Defect, "could not match module")
      # module may be nil to indicate that the transform applies to
      # the entire module graph as opposed to a single module
      yield decodeTransform(row[0], module, row[2])

iterator loadTransforms*(g: ModuleGraph;
                         modules: BModuleList; p: PSym): Transform =
  const
    selection = sql"""
      select transforms.kind, transforms.module, transforms.data
      from syms left join transforms
      where syms.name = transforms.signature and syms.name = ?
            and syms.module = ?
    """
  let
    name = $p.sigHash
    b = findModule(modules, p)
  for row in db.fastRows(selection, name, b.module.id):
    # search for the snippets for the given symbol
    let
      mid = if row[1] == "": 0 else: row[1].parseInt
    var
      module: BModule
    if mid == 0:
      # module may be nil to indicate that the transform applies to
      # the entire module graph as opposed to a single module
      yield decodeTransform(row[0], module, row[2])
    else:
      block found:
        # the modules in the modules list are in the modules list
        for m in modules.modules.items:
          if m != nil:
            # the module id is in the module's module field
            if m.module.id == mid:
              module = m
              break found
        # we didn't find the matching backend module; for now we throw
        raise newException(Defect, "could not match module")

proc loadTransformsIntoCache(cache: var CacheUnit) =
  ## read transforms from the database for the given cache node and merge
  ## them into the fake module graph
  let
    sig = sigHash(cache.node)
  for transform in cache.graph.loadTransforms(cache.modules, cache.node):
    case transform.kind
    of Unknown:
      raise newException(Defect, "unknown transform in the db")
    else:
      cache.transforms.add sig, transform

iterator loadSnippets*[T: CacheableObject](g; modules: BModuleList;
                       p: T): Snippet =
  ## sighash as input, along with the module
  ##
  ## section and code as output
  const
    selection = sql"""
      select syms.name, snippets.module, section, code
      from syms left join snippets
      where syms.name = snippets.signature and syms.name = ?
    """
  var
    count = 0
  let
    name = $sigHash(p)
  for row in db.fastRows(selection, name):
    count.inc
    let
      mid = row[1].parseInt

    # search for the snippets for the given symbol
    block found:
      if mid == 0:
        var
          snippet = newSnippet[T](p, nil, row[2].parseInt.TCFileSection)
        snippet.code = row[3].rope
        yield snippet
        #break found
        raise
      else:
        # the modules in the modules list are in the modules list
        for module in modules.modules.items:
          if module != nil:
            # the module id is in the module's module field
            if module.module.id == mid:
              var
                snippet = newSnippet[T](p, module,
                                           row[2].parseInt.TCFileSection)
              snippet.code = row[3].rope
              yield snippet
              break found
      # we didn't find the matching backend module; for now we throw
      raise newException(Defect, "could not match module")

when false:
  proc loadSnippet(g: ModuleGraph; id: SqlId): Snippet =
    const
      selection = sql"""
      select id,kind,nimid,code,symbol
      from snippets where id = ?
      """
    let
      row = db.getRow(selection, id)
    if row[0] == "":
      raise newException(Defect, "very bad news; no snippet id " & $id)
    result = Snippet(id: id, kind: parseInt(row[1]).TNodeKind,
                     nimid: parseInt(row[2]),
                     code: rope(row[3]))
    result.symbol = parseInt(row[4])

  proc decodeDeps(g: ModuleGraph; input: string): Snippets {.deprecated.} =
    for id in input.split(","):
      let
        id = parseInt(id)
      result[id] = loadSnippet(g, id)

  proc encodeDeps(deps: Snippets): string {.deprecated.} =
    for snippet in deps.items:
      if result.len == 0:
        result = $snippet.id
      else:
        result &= "," & $snippet.id

proc storeSnippet*(cache: var CacheUnit; s: Snippet) =
  let
    sig = sigHash(cache.node)
  # we add all snippets to the cache
  cache.snippets.add sig, s
  # but we only write to the db when the writable flag is set
  if cache.writable:
    template g(): ModuleGraph = cache.graph
    const
      insertion = sql"""
        insert into snippets (signature, module, section, code)
        values (?, ?, ?, ?)
      """
    db.exec(insertion, $sig, s.module.module.id, s.section.ord, $s.code)

proc snippetAlreadyStored(g: ModuleGraph; p: PSym): bool =
  ## compares symbol hash and symbol id
  if g.config.symbolFiles == disabledSf: return
  const
    query = sql"""
      select syms.id
      from syms left join snippets
      where snippets.signature = syms.name and syms.name = ? and syms.nimid = ?
      limit 1
    """
  let
    signature = $p.sigHash
  result = db.getValue(query, signature, p.id) != ""

proc storeSections(cache: var CacheUnit; parent: BModule;
                   child: BModule) =
  let
    sig = sigHash(cache.node)
  # copy the generated procs, etc.
  for section, rope in child.s.pairs:
    if rope != nil:
      when not defined(release):
        echo "\tsection ", section,  " length ", rope.len
      var
        snippet = newSnippet(cache.node, child, section)
      snippet.code = rope
      storeSnippet(cache, snippet)

proc store(cache: var CacheUnit; parent: BModule; child: BModule): State =
  ## miscellaneous ropes
  assert cache.writable, "attempt to write unwritable module to cache"

  assert parent.filename == child.filename
  assert parent.cfilename == child.cfilename

  cache.storeRope(parent, child.injectStmt)

  if parent.initProc.prc == nil and child.initProc.prc != nil:
    cache.storeProc(InitProc, parent, child.initProc)
  elif child.initProc.prc != nil:
    assert false
  if parent.preInitProc.prc == nil and child.preInitProc.prc != nil:
    cache.storeProc(PreInit, parent, child.preInitProc)
  elif child.preInitProc.prc != nil:
    assert false

  cache.storeHeaders parent, child

  # 0. flags
  if parent.flags != child.flags:
    let
      transform = Transform(kind: FlagSet, module: parent,
                            flags: child.flags - parent.flags)
    #parent.flags = child.flags
    storeTransform(cache, cache.node, transform)

  for pair in child.dataCache.data.items:
    if pair.key != nil:
      if nodeTableGet(parent.dataCache, pair.key) >= 0:
        let
          transform = Transform(kind: LiteralData, module: parent,
                                node: pair.key, val: pair.val)
        storeTransform(cache, cache.node, transform)

  ## ✅1. ropes to store per section
  cache.storeSections(parent, child)

  ## ✅2. ptypes to store
  cache.storeTypeStack(parent, child)

  cache.storeIdSets parent, child, ThingSet, declaredThings
  cache.storeIdSets parent, child, ProtoSet, declaredProtos

  cache.storeLabels(parent, child)
  result = Merge

proc store(cache: var CacheUnit[PNode]; orig: BModule): State =
  storeImpl cache, orig:
    cache.graph.storeNode(orig.module, cache.node)
  result = Merge

proc store(cache: var CacheUnit[PSym]; orig: BModule): State =
  storeImpl cache, orig:
    if cache.writable:
      if cache.node.typ == nil or cache.node.typ.sym == nil:
        echo "NIL FOUND"
    cache.graph.storeSym(cache.node)
  result = Merge

proc store(cache: var CacheUnit; parents: BModuleList): State =
  result = Done
  if cache.rejected:
    return

  #assert cache.writable, "attempt to write unwritable cache"
  template child(): BModuleList = cache.modules

  when not defined(release):
    echo "storing ", cache
  assert child != nil
  cache.storeRopes(parents, child.mainModProcs)
  cache.storeRopes(parents, child.mainModInit)
  cache.storeRopes(parents, child.otherModsInit)
  cache.storeRopes(parents, child.mainDatInit)
  cache.storeRopes(parents, child.mapping)

  for m in child.modules.items:
    if m != nil:
      var dad = findModule(parents, m)
      # dad is the final backend module in codegen
      if dad == nil:
        cache.reject {Reads, Writes}
        raise newException(Defect, "missing dad of " & $m.module.id)
      else:
        if result < Merge:
          if cache.writable:
            result = max(result, cache.store(m))
        result = max(result, cache.store(dad, m))
        if result > Merge:
          break
  if result == Store:
    raise newException(Defect, "unable to place node with a module")

  # good to go
  result = Merge

  when not defined(release):
    echo "\tstore yielding snippets      ", cache.snippets.len
    echo "\tstore yielding transforms    ", cache.transforms.len

proc loadSnippetsIntoCache*(cache: var CacheUnit) =
  ## read snippets from the database for the given cache node and merge
  ## them into the fake module graph
  let
    sig = sigHash(cache.node)
  for snippet in cache.graph.loadSnippets(cache.modules, cache.node):
    cache.snippets.add sig, snippet

proc apply(parents: BModuleList; snippet: Snippet) =
  assert snippet.module != nil
  let
    m = findModule(parents, snippet.module)
  #cache.snippets[snippet.signature] = snippet
  when not defined(release):
    echo "\t", snippet.section, "\t", snippet.module.module.id
  if m.s[snippet.section] == nil:
    m.s[snippet.section] = rope("")
  when false: # not defined(release):
    m.s[snippet.section].add fmt"""

/*
cached data from {snippet.section}
module: {m.cfilename}
*/

        """.rope
    m.s[snippet.section].add snippet.code
    when not defined(release):
      m.s[snippet.section].add "/* end */\n".rope

template loadImpl(cache: var CacheUnit; orig: BModule; body: untyped) =
  ## this needs to merely LOAD data so that later MERGE operations can work
  template g(): ModuleGraph = cache.graph
  when not defined(release):
    echo "load for ", cache, " ", orig
  if not cache.readable:
    raise newException(Defect, "attempt to read unreadable cache")

  # flush the stacks in case we need to read them
  cache.graph.storeRemaining(orig.module)

  body

  # read/apply snippets to the cache
  cache.loadSnippetsIntoCache

  # read/apply transforms to the cache
  cache.loadTransformsIntoCache

proc load(cache: var CacheUnit[PNode]; orig: BModule): State =
  ## this needs to merely LOAD data so that later MERGE operations can work
  loadImpl cache, orig:
    cache.node = cache.graph.loadNode(orig.module)
  result = max(Merge, cache.state)

proc load(cache: var CacheUnit[PSym]; orig: BModule): State =
  ## this needs to merely LOAD data so that later MERGE operations can work
  loadImpl cache, orig:
    # shadow the passed the modulelist because we probably want to rely upon
    # our faked cache modules instead
    var
      list = cache.modules

    # work around mutation of symbol
    if 0 == symbolId(cache.graph, cache.node):
      raise newException(Defect, "missing symbol: " & cache.node.name.s)
    let
      sym = cache.graph.loadSym(cache.node.id, cache.node.info)
    cache.node = sym
  result = max(Merge, cache.state)

proc nodeAlreadyStored(g: ModuleGraph; p: PNode): bool =
  const
    query = sql"""
      select id
      from toplevelstmts
      where signature = ?
      limit 1
    """
  let
    sig = p.sigHash
  result = db.getValue(query, $sig) != ""

proc isHot(cache: CacheUnit[PNode]): bool =
  if {Reads, Immutable} * cache.strategy != {Immutable}:
    result = nodeAlreadyStored(cache.graph, cache.node)

proc isHot(cache: CacheUnit[PSym]): bool =
  if {Reads, Immutable} * cache.strategy != {Immutable}:
    result = symbolAlreadyStored(cache.graph, cache.node)

proc newCacheUnit*[T: CacheableObject](modules: BModuleList; origin: BModule;
                  node: var T; strategy: set[CacheStrategy]): CacheUnit[T] =
  ## create a new cache unit object with the given strategy
  assert node != nil
  assert modules != nil
  result = CacheUnit[T](node: node, origin: origin,
                        graph: modules.graph)

  result.state = Initialize

  when not defined(release):
    if Reads in result.strategy:
      assert result.isHot

proc applyTransforms*(parents: BModuleList; transforms: TransformTable) =
  for transform in transforms.values:
    parents.apply transform
    {.warning: "maybe deposit the transform in the parent?".}

proc merge(cache: var CacheUnit; parents: var BModuleList): State =
  ## merging is as simple as applying the snippets and transforms,
  ## and then pointing the ast to its real module origin
  result = Abort
  echo "MERGE IN PROGRESS"
  if not cache.initialized:
    result = Done
    when not defined(release):
      echo "NOT merging ", cache, " ", $cache.origin
    return

  result = Abort
  when not defined(release):
    echo "merging ", cache, " ", $cache.origin

  when true:
    var
      c = initCountTable[TransformKind]()
    for v in cache.transforms.values:
      c.inc v.kind
    for k, v in c.pairs:
      echo k, " --> ", v

  for snippet in cache.snippets.values:
    parents.apply snippet

  for transform in cache.transforms.values:
    parents.apply transform

  assert cache.modules != nil
  assert cache.modules.modules.len > 0
  for module in cache.modules.modules.items:
    if module != nil:
      parents.applyTransforms module.transforms

  # good to go
  result = Done

  when false:
    # reset the owning module for the cache's node
    if cache.kind != Node:
      pointToModuleIn(addr cache.node.origin, parents)
    else:
      {.warning: "nodes unimplemented".}

proc setLocation*(m: BModule; p: PSym or PType; t: TLoc)
  {.tags: [TreeSafe, TreeRead, TreeWrite, RootEffect].} =
  ## set the location of a symbol|type in the given module
  #assert t.k != locNone, "set the kind at least"
  assert m != nil
  assert m.module != nil
  let mom = getModule(m.module)
  assert mom != nil
  when p is PSym:
    let id = p.id
    let k = nkSym
    assert p != nil
    let owner = getModule(p)
    assert owner != nil
    #  if getModule(p) == nil:
    #    p.owner = m.module
    {.warning: "add in guard for setloc in wrong module".}
    # assert abs(owner.id) == abs(mom.id)
  elif p is PType:
    let id = p.uniqueId
    let k = nkType
  else:
    {.fatal: "turn back!".}
  var transform = Transform(kind: SetLoc, module: m, nkind: k, id: id, loc: t)
  when p is PType:
    # use the sighash of the module symbol
    m.transforms.add m.module.sigHash, transform
  elif p is PSym:
    # see above
    m.transforms.add p.sigHash, transform
  else:
    {.fatal: "turn back!".}
  # TODO: witness
  p.setLocation(t)

proc inclLocationFlags*(m: BModule; p: PSym; f: set[TLocFlag] | TLocFlag) =
  ## set the location flags of a symbol in the given module
  var
    t = p.loc
  t.flags.incl f
  m.setLocation(p, t)

proc exclLocationFlags*(m: BModule; p: PSym; f: set[TLocFlag] | TLocFlag) =
  ## set the location flags of a symbol in the given module
  var t = p.loc
  t.flags.excl f
  m.setLocation(p, t)

proc setLocationRope*(m: BModule; p: PSym or PType; r: Rope) =
  ## set the symbol's location rope and then push the location
  ## into the module with a setLocation() for good measure
  var t = p.loc
  t.setRopeSecret r
  m.setLocation(p, t)

proc `$`(t: Transform): string =
  result = $t.kind & " from " & $t.nkind & " size " & $encodeTransform(t).len

proc commonCacheUnitInit[T](cache: var CacheUnit[T]; modules: BModuleList;
                            node: T): State =
  # add a container for relevant snippets
  result = cache.state
  let
    size = tables.rightSize(TCFileSection.high.ord)
  cache.snippets = initOrderedTable[SigHash, Snippet](size)
  # and transformations
  cache.transforms = initOrderedTable[SigHash, Transform](size * 16)

  # create a fake module graph
  cache.modules = createFakeGraph(modules, node)

  # initialize the cache unit and assign its kind
  #cache.initCacheUnit(modules, node)

  when false:
    # generic repoint ast to fake module
    if cache.kind != Node:
      pointToModuleIn(node.origin, cache.modules)

  # remove the read flag if the target isn't in the cache
  if not cache.isHot:
    cache.strategy.excl Reads

  # it's good to go
  cache.initialized = true

proc initCacheUnit(cache: var CacheUnit[PNode]; modules: BModuleList; node: PNode): State =
  cache.kind = CacheUnitKind.Node
  result = max(cache.state, cache.commonCacheUnitInit(modules, node))

proc initCacheUnit(cache: var CacheUnit[PSym]; modules: BModuleList; node: PSym): State =
  cache.kind = CacheUnitKind.Symbol
  result = max(cache.state, cache.commonCacheUnitInit(modules, node))

proc initCacheUnit(cache: var CacheUnit[PType]; modules: BModuleList; node: var PType): State =
  cache.kind = CacheUnitKind.Type
  result = cache.state
  # notably, not doing types

template mutateLocation*(m: BModule; p: PSym or PType; body: untyped): untyped =
  when true:
    # hide our dirty, dirty little secret
    proc setRope(l: var TLoc; roap: Rope) {.inject.} =
      setRopeSecret(l, roap)
    # hide our dirty, dirty little secret (v2)
    proc setRope(l: var TLoc; s: string) {.inject.} =
      setRopeSecret(l, rope(s))

  let l = p.loc
  var mloc {.inject.}: TLoc = l
  body
  block:
    if mloc != l:
      when p is PSym:
        if l.k != locNone and l.k != mloc.k:
          # XXX: I HATE CLYYBBER
          echo "loc was: ", $l
          echo "loc now: ", $mloc
          echo "symbol is ", p.id
          #writeStackTrace()
          #echo "-====================-"
          #raise
      setLocation(m, p, mloc)

proc setRope*(m: BModule; p: PSym or PType; roap: Rope) {.tags: [TreeSafe, TreeRead, TreeWrite, RootEffect].} =
  assert roap != nil
  when defined(debugTLoc):
    echo "set rope mut"
  mutateLocation(m, p):
    mloc.setRopeSecret roap

proc clearRope*(m: BModule; p: PSym or PType)
  {.tags: [TreeRead, TreeSafe, TreeWrite, RootEffect].} =
  when defined(debugTLoc):
    echo "clear mut"
  mutateLocation(m, p):
    mloc.setRopeSecret nil

template clearRope*(p: BProc; s: PSym or PType)
  {.tags: [TreeRead, TreeSafe, TreeWrite, RootEffect].} =
  clearRope(p.module, s)

template runMachine*(cache: var CacheUnit;
                     g: BModuleList; body: untyped): untyped =
  ## move between caching states
  var target = cache.findTargetModule(cache.origin)
  var p = cache.node
  var current = Invalid

  # the machine only runs in one direction: straight up
  while cache.state > current:
    current = cache.state
    case current
    of Invalid:
      raise
    # alloc or do expensive checks
    of Initialize:
      if cache.readable:
        cache.state = Load
      else:
        cache.state = Generate
    # load the data from cache
    of Load:
      if cache.initCacheUnit(g, p) == Load:
        cache.state = cache.load(cache.origin)
    # generate the data
    of Generate:
      if cache.initCacheUnit(g, p) == Generate:
        var
          m {.inject.}: BModule = target
        try:
          body
          # store also produces unstored mutations for later merge
          cache.state = Store
        except:
          cache.state = Abort
          cache.reject {Reads, Writes}
          raise
    # store the data to cache
    of Store:
      assert current == Generate
      cache.state = cache.store g
    # merge the cache unit into a global module graph
    of Merge:
      cache.state = cache.merge g
    # an abortion of the machine
    of Abort:
      cache.state = Done
      echo "cache abortion"
    # we're done
    of Done:
      break
    assert cache.state > current
  cache.state

template performCaching*(g: var BModuleList; origin: var BModule;
                         p: var CacheableObject; body: untyped): untyped =
  var
    # figure out if we're in a position to cache anything
    strategy = assignStrategy(g.config, p)
  strategy = {}
  if {Reads, Writes} * strategy == {}:
    var
      m {.inject.}: BModule = origin
    body
  else:
    var
      cache = newCacheUnit(g, origin, p, strategy)
    if State.high != runMachine(cache, g, body):
      raise newException(Defect, "cache machine fail")
