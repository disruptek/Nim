#
#
#           The Nim Compiler
#        (c) Copyright 2017 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#
# ------------------------- Name Mangling --------------------------------
##[

cgendata defines ConflictsTable as Table[string, int]

The key has one of two forms:
  "someMangledName" -> the output of mangle() on a symbol or
  "someMangledName" -> the output of getTypeName() on a type or
  "######" -> a series of digits representing a unique symbol or type id

The values have different meanings depending upon the form of the key:
  "someMangledName" -> the value represents the next available counter
  "######" -> the value represents the counter associated with the id

The counter is used to keep track of the order of symbol additions to the
conflict table; they are increasing but not guaranteed to be sequential.

]##

import # compiler imports

    ast, cgendata, modulegraphs, ropes, ccgutils, ndi, msgs, incremental,
    idents, options, wordrecg, astalgo, treetab, sighashes

import # stdlib imports

  std / [ strutils, tables, sets ]

const
  inspect = "arrClong"
  symbolicTypes =
    when true:
      {tyObject, tyEnum} # obey the boss
    else:
      {tyObject, tyEnum, tyString}
  addFirstParamToProcs = true
  findSourceModulesForTypes = true
  hashTypeOptions = {CoType} #, CoNaming}
  debugMangle = true and not defined(release)

  # these may be shorted to the first three characters following `ty`
  # as opposed to perhaps being stripped of vowels, etc.
  threeLetterShorties = {tyOrdinal, tySequence, tyObject, tyTuple, tyArray,
                         tyVar, tyPtr, tyString, tySet, tyRef, tyTypeDesc}
  # these are types that we ignore entirely when mangling
  irrelevantForNaming = irrelevantForBackend + {tyVar} - {tyRange}
  # these types may prefix the types they wrap, eg. `seqStr` or `setInt`
  abbrevTypeArg = {tySet, tySequence, tyTypeDesc, tyArray, tyRange}
  # these types get unwrapped and discarded from mangling
  unwrapTypeArg = irrelevantForNaming - {tyRange} + {tyRef, tyPtr,
                                         tyUserTypeClass, tyUserTypeClassInst}

type
  ModuleOrProc* = BProc or BModule

template config(): ConfigRef = cache.modules.config
template add_and(s: typed; chs: string) = s.add "_"; s.add chs

using
  g: ModuleGraph

# get a unique id from a psym or ptype; these are keys in ConflictsTable
template conflictKey(s: PSym): int = s.id
template conflictKey(s: PType): int = s.uniqueId

# useful for debugging
template conflictKey(s: BModule): int = conflictKey(s.module)
template conflictKey(s: BProc): int =
  if s.prc == nil:
    0
  else:
    conflictKey(s.prc)

proc mangle*(p: ModuleOrProc; s: PSym): string
proc mangleName*(p: ModuleOrProc; s: PSym): Rope
proc typeName(p: ModuleOrProc; typ: PType; shorten = false): string

proc `==`(m, p: BModule): bool =
  if not p.isNil and not m.isNil:
    result = p.module.id == m.module.id
    result = result and p.cfilename.string == m.cfilename.string

proc hashTypeDef*(p: PType): SigHash =
  ## A hash of the type that may eventually discern between distinct and
  ## alias; this is used to separate entries in the typecaches
  result = hashType(p, hashTypeOptions)
  when debugMangle:
    if startsWith($result, inspect):
      if p.sym != nil:
        echo mangle(p.sym.name.s), " --> ", result

proc getSomeNameForModule*(m: PSym): string =
  ## Produce a name for the given module symbol.
  assert m.kind == skModule
  assert m.owner.kind == skPackage
  if {sfSystemModule, sfMainModule} * m.flags == {}:
    result = mangle(m.owner.name.s)
    result.add "_"
    assert m.name.s.len > 0
  result.add mangle(m.name.s)
  if result.startsWith("stdlib_"):
    # replaceWord will consume _ :-(
    result = "std_" & result[len("stdlib_") .. ^1]

proc findPendingModule*(m: BModule; s: PSym): BModule =
  ## Find the backend module to which a symbol belongs.
  if s == nil:
    result = m
  else:
    var ms = getModule(s)
    result = m.g.modules[ms.position]

proc findPendingModule*(m: BModule; t: PType): BModule =
  ## Find the backend module to which a type belongs.
  if t.owner == nil:
    result = findPendingModule(m, t.sym)
  else:
    result = findPendingModule(m, t.owner)
    #echo "parent owner of type ", conflictKey(t), " is ", result.module.id
  #echo "parent result of type ", conflictKey(t), " is ", result.module.id
  #echo "parent sym of type ", conflictKey(t), " is ", findPendingModule(m, t.sym).module.id

proc isNimOrCKeyword*(w: PIdent): bool =
  # Nim and C++ share some keywords
  # it's more efficient to test the whole Nim keywords range
  case w.id
  of ccgKeywordsLow..ccgKeywordsHigh:
    true
  of nimKeywordsLow..nimKeywordsHigh:
    true
  of ord(wInline):
    true
  else:
    false

proc `[]`(conflicts: var ConflictsTable; s: string): int =
  result = getOrDefault(conflicts, s, if s[0].isDigit: -1 else: 0)

proc `[]=`(conflicts: var ConflictsTable; s: string; v: int) =
  var existing = mgetOrPut(conflicts, s, v)
  when debugMangle:
    if s[0].isDigit:
      if existing != v:
        assert false, "attempt to reindex " & s
  if existing < v:
    existing = v
    # working around an apparent bug in that we cannot modify existing...
    tables.`[]=`(conflicts, s, v)
  elif existing > v:
    when debugMangle:
      echo "ignore low adjustment of ", s

proc getOrSet(p: ModuleOrProc; name: string; key: int): int =
  ## Add/get a mangled name from the scope's conflicts table and return
  ## the number of conflicts for that name at the time of its insertion.
  template conflicts(): var ConflictsTable = p.sigConflicts
  let key = $key

  when false:
    when debugMangle:
      if $conflictKey(p) == "14581015":
        if key in ["18165280", "18256094"]:
          echo "(symbol or type code) ", key
          echo "counter associated with the symbol/type ", conflicts[key]
          echo "counter associated with the name ", conflicts[name]

  result = getOrDefault(conflicts, key, -1)
  if result == -1:
    when debugMangle:
      if startsWith(name, inspect):
        echo "getorset on ", $typeof(p), " ", conflictKey(p), " addr ", cast[uint](p), " table ", cast[uint](addr conflicts)
        when p is BModule:
          echo "getorset (module) ", p.cfilename.string
          echo "getorset (module) ", p.module.flags
        else:
          echo "getorset (proc) ", p.prc.name.s

    # start counting at zero so we can omit an initial append
    result = getOrDefault(conflicts, name, 0)
    # set the value for the name to indicate the NEXT available counter
    conflicts[name] = result + 1
    # cache the association between key and result
    conflicts[key] = result

    when debugMangle:
      if startsWith(name, inspect):
        echo "getorset at ", $conflictKey(p), " for ", name, " with key ", key, " is ", result

  else:
    when debugMangle:
      if result > conflicts[name]:
        internalError(p.config, "clash count unexpectedly low")

proc nextConflict(p: ModuleOrProc; name: string; key: int): int {.deprecated.} =
  let skey = $key
  if skey in p.sigConflicts:
    result = p.sigConflicts[skey]
  else:
    result = p.sigConflicts[name]

proc floatConflict(m: BModule; s: PSym; name: string; key: int): int =
  ## Mix a local name into any parent scopes of symbol `s`.
  let p = findPendingModule(m, s)
  # first update the parent of the type
  result = getOrSet(p, name, key)
  if p != m:
    # cache the counter in the local module
    m.sigConflicts[$key] = result
    # set the local name to prevent future conflict
    m.sigConflicts[name] = p.sigConflicts[name]

proc floatConflict(p: BProc; s: PSym; name: string; key: int): int =
  ## Mix a local name into any parent scopes of symbol `s`.
  let m = p.module
  # first update the parent of the symbol
  result = floatConflict(m, s, name, key)
  # cache the counter in the local proc
  p.sigConflicts[$key] = result
  # set the local name to prevent future conflict
  p.sigConflicts[name] = m.sigConflicts[name]

proc floatConflict(m: BModule; t: PType; name: string; key: int): int =
  ## Mix a local name into any parent scopes of type `t`.
  let p = findPendingModule(m, t)
  # first update the parent of the type
  result = getOrSet(p, name, key)
  if p != m:
    # cache the counter in the local module
    m.sigConflicts[$key] = result
    # set the local name to prevent future conflict
    m.sigConflicts[name] = p.sigConflicts[name]

proc purgeConflict*(m: ModuleOrProc; s: PSym) =
  ## We currently only use this to remove parameters from a conflict table
  ## in a module so they can be added into the table in the proc itself.
  del m.sigConflicts, $conflictKey(s)

proc hasImmutableName(s: PSym): bool =
  ## True if the symbol uses a name that must not change.
  const immut = {sfSystemModule, sfCompilerProc, sfImportc, sfExportc}
  result = s == nil
  if not result:
    # special-casing FlowVars because they are special-cased in pragmas...
    if sfCompilerProc in s.flags:
      if not s.typ.isNil and s.typ.kind == tyGenericBody:
        assert s.name.s == "FlowVar", "unexpected generic compiler proc"
        return false
    result = immut * s.flags != {}

proc shouldAddModuleName(s: PSym): bool =
  ## Are we going to apply top-level mangling semantics?
  assert not s.hasImmutableName
  case s.kind
  of skParam, skResult, skModule, skPackage, skTemp:
    result = false
  of skConst:
    # NOTE: constants are effectively global
    result = true
  else:
    if s.owner != nil and sfSystemModule in s.owner.flags:
      # omit "system" in the interests of brevity
      result = false
    elif s.owner == nil or s.owner.kind in {skModule, skPackage}:
      # the symbol is top-level; add the module name
      result = true
    elif {sfGlobal, sfGeneratedOp} * s.flags != {}:
      # the symbol is top-level; add the module name
      result = true
    elif s.kind == skForVar:
      # forvars get special handling due to the fact that they
      # can, in rare and stupid cases, be globals...
      result = false
    elif sfExported in s.flags:
      # exports get their source module appended
      result = true

proc shortKind(k: TTypeKind): string =
  ## truncate longer type names
  const vowels = {'a','e','i','o','u'}
  result = toLowerAscii($k)
  removePrefix(result, "ty")
  result = case k
  # handle der usual suspects especialment
  of threeLetterShorties:
    result[0 .. 2]
  elif len(result) > 4:  # elide vowels to shrink it
    if result[0] in vowels:
      # if it starts with a vowel, keep that letter; think `Opnrry`, `Unt32`
      $result[0] & split(result[1..^1], vowels).join("")
    else:
      split(result, vowels).join("")
  else: result

proc naiveTypeName(p: ModuleOrProc; typ: PType; shorten = false): string =
  ## compose a type name for a type that has an unusable symbol
  var typ = typ.skipTypes(irrelevantForNaming)
  result = case typ.kind
  of abbrevTypeArg:
    # set[Enum] -> setEnum for "first word" shortening purposes
    shortKind(typ.kind) & typeName(p, typ.lastSon, shorten).capitalizeAscii
  of unwrapTypeArg:
    # omit this verbosity for now and simply discard the wrapper
    typeName(p, typ.lastSon, shorten = shorten)
  of tyProc, tyTuple:
    # these can figure into the signature though they may not be exported
    # as types, so signature won't match when it comes time to link

    # these are not just a c++ problem... m.config.backend == backendCpp:

    # best idea i can come up with is a global registry where we simply
    # record the first introduction of an otherwise unknown signature and
    # always reuse it

    # these need a signature-based name so that type signatures match :-(
    shortKind(typ.kind) & $hashTypeDef(typ)
  else:
    shortKind(typ.kind)

proc typeName(p: ModuleOrProc; typ: PType; shorten = false): string =
  ## Come up with a name for any PType; shorten makes it shorter. 😉
  var typ = typ.skipTypes(irrelevantForNaming)
  if typ.sym == nil or typ.kind notin symbolicTypes:
    # we have to come up with our own name...
    naiveTypeName(p, typ, shorten = shorten)
  elif shorten:
    # do the complete mangle but only use the first "word"
    mangle(p, typ.sym).split("_")[0]
  else:
    # use the complete type symbol mangle
    mangle(p, typ.sym)

template maybeAddCounter(result: typed; count: int) =
  if count > 0:
    add_and result, $count

proc maybeAddProcArgument(p: ModuleOrProc; s: PSym; name: var string): bool =
  ## Should we add the first argument's type to the mangle?  If yes, DO IT.
  result = s.kind in routineKinds
  if result:
    # disabled for now because i can't figure out how to handle aliases
    when addFirstParamToProcs:
      if s.typ != nil:
        if s.typ.sons.len >= 2:
          # avoid including the conflictKey of the 1st param
          name.add_and typeName(p, s.typ.sons[1], shorten = true)
    else:
      # procs are distinguished with an extra _ to prevent type clash
      name.add "_"

proc mayCollide(p: ModuleOrProc; s: PSym; name: var string): bool =
  ## `true` if the symbol is a source of link collisions; if so,
  ## the name is set to a suitable mangle
  name = ""
  try:
    case s.kind
    of skProc:
      # anonymous procs are special for... reasons
      result = s.name.s == ":anonymous"
      if result:
        name.add "lambda_"
      # var procs are fun; generated proc names, too
      result = result or {sfAddrTaken, sfGenSym} * s.flags != {}
      # closures are great for link collisions
      result = result or tfCapturesEnv in s.typ.flags
    of skIterator:
      result = true
    # a gensym is a good sign that we can encounter a link collision
    elif sfGenSym in s.flags:
      result = true
  finally:
    if result:
      if name.len == 0:
        name = mangle(s.name.s)
      name.add_and $conflictKey(s)
      assert not s.hasImmutableName

proc mangle*(p: ModuleOrProc; s: PSym): string =
  # TODO: until we have a new backend ast, all mangles have to be done
  # identically
  let m = getem()

  # certain special cases may get a simple mangle early because
  # we must be assured of their consistent clash-free linkage
  if not mayCollide(p, s, result):

    # otherwise, start off by using a name that doesn't suck
    result = mangle(s.name.s)

    # some symbols have flags that preclude further mangling
    if not s.hasImmutableName:

      # add the first argument to procs if possible
      discard maybeAddProcArgument(m, s, result)

      # add the module name if necessary, or if it helps avoid a clash
      if shouldAddModuleName(s) or isNimOrCKeyword(s.name):
        let parent = findPendingModule(m, s)
        if parent != nil:
          result.add_and getSomeNameForModule(parent.module)

      # for c-ish backends, "main" is already defined, of course
      elif s.name.s == "main":
        let parent = findPendingModule(m, s)
        if parent != nil and sfMainModule in parent.module.flags:
          # but we'll only worry about it for MainModule
          result.add_and getSomeNameForModule(parent.module)

      # something like `default` might need this check
      if (unlikely) result in m.config.cppDefines:
        result.add_and $conflictKey(s)

  #if getModule(s).id.abs != m.module.id.abs: ...creepy for IC...
  # XXX: we don't do anything special with regard to m.hcrOn
  assert result.len > 0

when not nimIncremental:
  proc getConflictFromCache(g: ModuleGraph; s: PSym): int =
    discard
else:
  import std/db_sqlite

  proc getConflictFromCache(g: ModuleGraph; s: PSym): int =
    template db(): DbConn = g.incr.db
    const
      query = sql"""
        select id from conflicts
        where nimid = ?
        order by id desc
        limit 1
      """
      insert = sql"""
        insert into conflicts (nimid)
        values (?)
      """
    let id = db.getValue(query, s.id)
    if id == "":
      # set the counter to the row id, not the symbol id or the actual count
      result = db.insertID(insert, s.id).int
    else:
      result = id.parseInt
    assert result > 0

proc atModuleScope(p: ModuleOrProc; s: PSym): bool =
  ## `true` if the symbol is presumed to be in module-level scope
  ## for the purposes of conflict detection
  const
    globalish = {sfImportc, sfGlobal, sfGeneratedOp, sfExportc, sfExported}

  # NOTE: constants and types are effectively global
  result = s.kind in {skConst, skType}
  # anything global or otherwise exported or imported is at module scope
  result = result or globalish * s.flags != {}

  when p is BProc:
    # if it's nominally proc but has no proc symbol, then we'll use
    # the module scope for conflict resolution; this solves a fun
    # corner-case where we have a toplevel forVar in an inline iterator
    result = result or p.prc.isNil

proc atModuleScope(p: ModuleOrProc; t: PType): bool =
  ## `true` if the type is presumed to be in module-level scope
  ## for the purposes of conflict detection
  result = t.sym == nil or atModuleScope(p, t.sym)

proc getSetConflict(p: ModuleOrProc; s: PSym): tuple[name: string; counter: int] =
  ## Produce an appropriate name for a symbol, and the instances of its
  ## occurence, which may have been incremented for this instance.
  let m = getem()
  template g(): ModuleGraph = m.g.graph
  var counter = -1         # the current counter for this name

  # we always mangle it anew, which is kinda sad
  var name = mangle(p, s)
  let key = $conflictKey(s)

  block:
    when p is BModule:
      if g.config.symbolFiles != disabledSf:
        # we can use the IC cache to determine the right name and counter
        # for this symbol, but only for module-level manglings
        counter = getConflictFromCache(g, s)
        break

    if atModuleScope(p, s):
      # critically, we must check for conflicts at the source module
      # in the event a global symbol is actually foreign to `p`
      counter = floatConflict(p, s, name, conflictKey(s))
      break

  # only write mangled names for c codegen
  when m is BModule:
    # and only if they aren't temporaries
    if s.kind != skTemp:
      # cache the symbol for write at file close
      writeMangledName(m.ndi, s, m.config)

  # if the counter hasn't been set from a foreign or cached symbol,
  if counter == -1:
    # set it using the local conflicts table
    counter = getOrSet(p, name, conflictKey(s))

  result = (name: name, counter: counter)

proc idOrSig*(p: ModuleOrProc; s: PSym): Rope =
  ## Provide the location rope for symbol `s` as used in module|proc `p`.
  when debugMangle:
    if s.name.s == inspect:
      echo "p is module ", p is BModule
      echo "p key ", $conflictKey(p)

  let conflict = getSetConflict(p, s)
  result = conflict.name.rope
  result.maybeAddCounter conflict.counter
  when debugMangle:
    if startsWith($result, inspect):
      debug s
      when p is BModule:
        result = "/*" & $conflictKey(s) & "*/" & result
        debug p.cfilename.string
        debug "module $4 >> $1 .. $2 -> $3" %
          [ $conflictKey(s), s.name.s, $result, $conflictKey(p.module) ]
      elif p is BProc:
        result = "/*" & $conflictKey(s) & "*/" & result
        debug "  proc $4 >> $1 .. $2 -> $3" %
          [ $conflictKey(s), s.name.s, $result,
           if p.prc != nil: $conflictKey(p.prc) else: "(nil)" ]

proc getCachedTypeName*(m: BModule; sig: SigHash): Rope {.deprecated.} =
  ## Try to get a cached type name from any and all modules.
  # there's a good chance it's in the local cache
  result = cacheGetType(m.typeCache, sig)
  if result == nil:
    # else, search the caches of the other modules
    for peer in items(m.g.modules):
      if peer != nil:
        # skip checking our own cache again
        if peer != m:
          result = cacheGetType(peer.typeCache, sig)
          if result != nil:
            break
  # instantiate a new rope for mutation reasons
  result = rope $result

proc getTypeName*(p: ModuleOrProc; typ: PType): Rope =
  ## Produce a useful name for the given type; this is what codegen uses
  ## when a SigHash is not available.
  var m = getem()

  # we don't currently use the proc scope for types; this is just a guard
  # to ensure that we don't do so accidentally
  var p = m

  var t = typ
  var name: string
  block found:
    # try to find the actual type
    while true:
      # use an immutable symbol name if we find one
      if t.sym != nil and hasImmutableName(t.sym):
        # the symbol might need mangling, first
        result = mangleName(p, t.sym)
        name = $result
        break found
      elif t.kind in irrelevantForNaming:
        t = t.lastSon    # continue into more precise types
      else:
        break            # this looks like a good place to stop

    assert t != nil
    name = typeName(p, t)

  when false:
    # the idea was to fix arrInt but it breaks seqTup so... :-(
    # we could pass a flag down through typeName i guess.
    if t.sym == nil:
      name.add "_" & $conflictKey(t)

  result = name.rope

  var counter: int
  when findSourceModulesForTypes:
    if atModuleScope(p, t):
      # make sure we use the source module for any type requested
      counter = floatConflict(p, t, name, conflictKey(t))
    else:
      # get the counter from the local proc or module
      counter = getOrSet(p, name, conflictKey(t))
  else:
    counter = getOrSet(p, name, conflictKey(t))

  # pthread_mutex_t
  if not hasImmutableName(t.sym):
    result.maybeAddCounter counter

  when debugMangle:
    if inspect in $result:
      echo "type mangle used:"
      debug t
      echo "=> ", conflictKey(m), " >> ", $result, spaces(4), $hashTypeDef(t)

    if inspect in $result:
      echo "original type mangle:"
      debug typ
      result.add "/*" & $conflictKey(typ) & "*/"
      echo "-> ", conflictKey(m), " >> ", $result, spaces(4), $hashTypeDef(typ)

  if result == nil:
    internalError(m.config, "getTypeName: " & $typ.kind)

proc getTypeName*(p: ModuleOrProc; typ: PType; sig: SigHash): Rope =
  ## Retrieve (or produce) a useful name for the given type; this is what
  ## codegen uses exclusively.
  result = getTypeName(p, typ)

template tempNameForLabel(m: BModule; label: int): string =
  ## create an appropriate temporary name for the given label
  m.tmpBase & $label & "_"

proc hasTempName*(m: BModule; n: PNode): bool {.deprecated: "but why?".} =
  ## True if the module/proc has a temporary cached for the given node.
  result = nodeTableGet(m.dataCache, n) != low(int)

proc getTempNameImpl(m: BModule; id: int): string =
  ## the only way to create a new temporary name in a given module
  assert id == m.labels
  # it's a new temporary; increment our counter
  inc m.labels
  # get the appropriate name
  result = tempNameForLabel(m, id)
  # (result ends in _)
  assert result.endsWith("_")
  # make sure it's not in the conflicts table
  assert result notin m.sigConflicts
  # put it in the conflicts table with the NEXT available counter
  m.sigConflicts[result] = 1

proc getTempName*(m: BModule; n: PNode; r: var Rope): bool =
  ## Create or retrieve a temporary name for the given node; returns
  ## true if a new name was created and false otherwise.  Appends the
  ## name to the given rope.
  let id = nodeTableTestOrSet(m.dataCache, n, m.labels)
  var name: string
  if id == m.labels:
    name = getTempNameImpl(m, id)
    result = true
  else:
    name = tempNameForLabel(m, id)
    # make sure it's not in the conflicts table under a different id
    assert getOrDefault(m.sigConflicts, name, 1) == 1
    # make sure it's in the conflicts table with the NEXT available counter
    m.sigConflicts[name] = 1

  # add or append it to the result
  if r == nil:
    r = name.rope
  else:
    r.add name

proc getTempName*(m: BModule; n: PNode): Rope =
  ## A simpler getTempName that doesn't care where the name comes from.
  discard getTempName(m, n, result)

proc getTempName*(m: BModule): Rope =
  ## A factory for making temporary names for use in the backend; this
  ## mutates the module from which the name originates; this always
  ## creates a new name.
  result = getTempNameImpl(m, m.labels).rope

proc mangleName*(p: ModuleOrProc; s: PSym): Rope =
  ## Mangle the symbol name and set a new location rope for it, returning
  ## same.  Has no effect if the symbol already has a location rope.
  if s.loc.r == nil:
    when p is BModule:
      # skParam is valid for global object fields with proc types
      #assert s.kind notin {skParam, skResult}
      assert s.kind notin {skResult}
    when p is BProc:
      assert s.kind notin {skModule, skPackage}
    s.loc.r = idOrSig(p, s)
  result = s.loc.r

    #[

     2020-06-11: leaving this here because it explains a real scenario,
                 but it remains to be seen if we'll still have this problem
                 after the new mangling processes the symbols; ie. why is
                 HCR special?

     Take into account if HCR is on because of the following scenario:

     if a module gets imported and it has some more importc symbols in it,
     some param names might receive the "_0" suffix to distinguish from
     what is newly available. That might lead to changes in the C code
     in nimcache that contain only a parameter name change, but that is
     enough to mandate recompilation of that source file and thus a new
     shared object will be relinked. That may lead to a module getting
     reloaded which wasn't intended and that may be fatal when parts of
     the current active callstack when performCodeReload() was called are
     from the module being reloaded unintentionally - example (3 modules
     which import one another):

       main => proxy => reloadable

     we call performCodeReload() in proxy to reload only changes in
     reloadable but there is a new import which introduces an importc
     symbol `socket` and a function called in main or proxy uses `socket`
     as a parameter name. That would lead to either needing to reload
     `proxy` or to overwrite the executable file for the main module,
     which is running (or both!) -> error.

    ]#

proc mangleField*(m: BModule; name: PIdent): string =
  ## Mangle a field to ensure it is a valid name in the backend.
  result = mangle(name.s)
  #[
   Fields are tricky to get right and thanks to generic types producing
   duplicates we can end up mangling the same field multiple times.
   However if we do so, the 'cppDefines' table might be modified in the
   meantime meaning we produce inconsistent field names (see bug #5404).
   Hence we do not check for ``m.g.config.cppDefines.contains(result)``
   here anymore:
  ]#
  if isNimOrCKeyword(name):
    result.add_and "0"

proc mangleRecFieldName*(m: BModule; field: PSym): Rope =
  ## Mangle an object field to ensure it is a valid name in the backend.
  if {sfImportc, sfExportc} * field.flags != {}:
    result = field.loc.r
  else:
    result = mangleField(m, field.name).rope
  if result == nil:
    internalError(m.config, field.info, "mangleRecFieldName")

proc mangleParamName*(m: BModule; s: PSym): Rope =
  ## We should be okay with just a simple mangle here for prototype
  ## purposes; the real meat happens when we're called with BProc...
  if s.loc.r == nil:
    if s.kind == skResult:
      s.loc.r = ~"result"
    else:
      # this is a little subtle; we need a mangle sophisticated enough
      # to rename `default`, and correct enough to match a later mangle,
      # but we don't want to actually getSetConflict() because we don't
      # want param names to be numbered as if they might clash due to
      # the module-level scope of the conflicts table...
      s.loc.r = mangle(m, s).rope
  result = s.loc.r
  if result == nil:
    internalError(m.config, s.info, "mangleParamName")

proc mangleParamName*(p: BProc; s: PSym): Rope =
  ## Push the mangled name into the proc's sigConflicts so that we can
  ## make new local identifiers of the same name without colliding with it.

  # It's likely that the symbol is already in the module scope!
  if s.loc.r == nil or $conflictKey(s) notin p.sigConflicts:
    # discard any existing counter for this sym from the module scope
    purgeConflict(p.module, s)
    if s.kind == skResult:
      s.loc.r = ~"result"        # just set it to result if it's skResult
      # record (and verify) the result in the local conflicts table
      if getOrSet(p, "result", conflictKey(s)) != 0:
        internalError(p.config, s.info, "assignParam: shadowed result")
    else:
      s.loc.r = nil              # critically, destroy the location
      s.loc.r = mangleName(p, s) # then mangle it using the proc scope
  result = s.loc.r
  if result == nil:
    internalError(p.config, s.info, "mangleParamName")

proc assignParam*(p: BProc, s: PSym; ret: PType) =
  discard #mangleParamName(p, s)
