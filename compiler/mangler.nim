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
  "SomeMangledName" -> the output of mangle() on a symbol
  "######" -> a series of digits representing a unique symbol or type id

The values have different meanings depending upon the form of the key:
  "SomeMangledName" -> the value represents the next available counter
  "######" -> the value represents the counter associated with the id

The counter is used to keep track of the order of symbol additions to the
conflict table; they are increasing but not guaranteed to be sequential.

]##


import # compiler imports

    ast, cgendata, modulegraphs, ropes, ccgutils, ndi, msgs, incremental,
    idents, options, wordrecg, astalgo, treetab, sighashes

import # stdlib imports

  std / [ strutils, tables, sets ]

type
  ModuleOrProc* = BProc or BModule

template config(): ConfigRef = cache.modules.config

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
proc typeName*(p: ModuleOrProc; typ: PType; shorten = false): string

proc getSomeNameForModule*(m: PSym): string =
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

proc findPendingModule*(m: BModule, s: PSym): BModule =
  var ms = getModule(s)
  result = m.g.modules[ms.position]

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

proc getOrSet(conflicts: var ConflictsTable; name: string; key: int): int =
  ## Add/get a mangled name from the conflicts table and return the number
  ## of conflicts for that name at the time of its insertion.
  let key = $key
  result = getOrDefault(conflicts, key, -1)
  if result == -1:
    # start counting at zero so we can omit an initial append
    result = getOrDefault(conflicts, name, 0)
    if result == 0:
      # set the value for the name to indicate the NEXT available counter
      conflicts[name] = 1
    else:
      # this is kinda important; only an idiot would omit it on his first try
      inc conflicts[name]
    # cache the result associated with the key
    conflicts[key] = result

proc purgeConflict*(m: ModuleOrProc; s: PSym) =
  ## We currently only use this to remove parameters from a conflict table
  ## in a module so they can be added into the table in the proc itself.
  del m.sigConflicts, $conflictKey(s)

proc hasImmutableName(s: PSym): bool =
  ## True if the symbol uses a name that must not change.
  const immut = {sfSystemModule, sfCompilerProc, sfImportc, sfExportc}
  if s != nil:
    # special-casing FlowVars because they are special-cased in pragmas...
    if sfCompilerProc in s.flags:
      if not s.typ.isNil and s.typ.kind == tyGenericBody:
        assert s.name.s == "FlowVar", "unexpected generic compiler proc"
        return false
    result = immut * s.flags != {}

proc shouldAppendModuleName(s: PSym): bool =
  ## Are we going to apply top-level mangling semantics?
  assert not s.hasImmutableName
  case s.kind
  of skParam, skResult, skModule, skPackage, skTemp:
    result = false
  of skConst:
    # NOTE: constants are effectively global
    result = true
  else:
    if s.owner == nil or s.owner.kind in {skModule, skPackage}:
      # the symbol is top-level; add the module name
      result = true
    elif {sfGlobal, sfGeneratedOp} * s.flags != {}:
      # the symbol is top-level; add the module name
      result = true
    elif s.kind == skForVar:
      # forvars get special handling due to the fact that they
      # can, in rare and stupid cases, be globals...
      result = false

    # exports get their source module appended
    if sfExported in s.flags:
      result = true

const
  irrelevantForBackend* = {tyGenericBody, tyGenericInst, tyOwned,
                           tyGenericInvocation, tyDistinct, tyRange,
                           tyStatic, tyAlias, tySink, tyInferred}
  threeLetterShorties = {tyRef, tySequence, tyObject, tyTuple, tyArray,
                         tyPtr, tyString, tySet, tyOrdinal, tyTypeDesc}
  unwrapTypeArg = {tyRef, tyPtr, tySet, tySequence, tyTypeDesc, tyArray}

proc shortKind(k: TTypeKind): string =
  ## truncate longer type names
  const vowels = {'a','e','i','o','u'}
  result = toLowerAscii($k)
  removePrefix(result, "ty")
  # TODO: currently, uint32 -> nt32 🙁
  result = case k
  # handle der usual suspects especialment
  of threeLetterShorties:
    result[0 .. 2]
  elif len(result) > 4:  # elide vowels to shrink it
    if result[0] in vowels:
      # if it starts with a vowel, keep that letter; think `Opnrry`
      split(result[1..^1], vowels).join("")
    else:
      split(result, vowels).join("")
  else: result

proc naiveTypeName(p: ModuleOrProc; typ: PType; shorten = false): string =
  ## compose a type name for a type that has an unusable symbol
  case typ.kind
  of unwrapTypeArg:
    # set[Enum] -> setEnum for "first word" shortening purposes
    shortKind(typ.kind) & typeName(p, typ.lastSon, shorten).capitalizeAscii
  of tyVar:
    # omit this verbosity for now and simply discard the var
    typeName(p, typ.lastSon, shorten = shorten)
  of tyProc, tyTuple:
    # these can figure into the signature though they may not be exported
    # as types, so signature won't match when it comes time to link

    # these are not just a c++ problem... m.config.backend == backendCpp:

    # best idea i can come up with is a global registry where we simply
    # record the first introduction of an otherwise unknown signature and
    # always reuse it

    # these need a signature-based name so that type signatures match :-(
    shortKind(typ.kind) & $hashType(typ)
  else:
    shortKind(typ.kind)

proc typeName*(p: ModuleOrProc; typ: PType; shorten = false): string =
  ## Come up with a name for any PType; shorten makes it shorter. 😉
  var typ = typ.skipTypes(irrelevantForBackend)
  if typ.sym == nil:
    # there's no symbol, so we have to come up with our own name...
    naiveTypeName(p, typ, shorten = shorten)
  elif shorten:
    # do the complete mangle but only use the first "word"
    mangle(p, typ.sym).split("_")[0]
  else:
    # use the complete type symbol mangle
    mangle(p, typ.sym)

template maybeAddCounter(result: typed; count: int) =
  if count > 0:
    result.add "_"
    result.add $count

proc maybeAddProcArgument(p: ModuleOrProc; s: PSym; name: var string): bool =
  ## Should we add the first argument's type to the mangle?  If yes, DO IT.
  if s.kind in routineKinds:
    if s.typ != nil:
      result = s.typ.sons.len >= 2
      if result:
        name.add "_"
        # avoid including the conflictKey of the 1st param
        name.add typeName(p, s.typ.sons[1], shorten = true)

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
      # var procs are fun
      result = result or sfAddrTaken in s.flags
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
      name.add "_"
      name.add $conflictKey(s)
      assert not s.hasImmutableName

proc mangle*(p: ModuleOrProc; s: PSym): string =
  # TODO: until we have a new backend ast, all mangles have to be done
  # identically
  let m = getem()
  block:
    if mayCollide(p, s, result):
      # result is now populated with a mangled name
      break

    # otherwise, start off by using a name that doesn't suck
    result = mangle(s.name.s)

  # some symbols have flags that preclude further mangling
  if not s.hasImmutableName:

    # add the first argument to procs if possible
    discard maybeAddProcArgument(m, s, result)

    # add the module name if necessary, or if it helps avoid a clash
    if shouldAppendModuleName(s) or isNimOrCKeyword(s.name):
      let parent = findPendingModule(m, s)
      if parent != nil:
        result.add "_"
        result.add getSomeNameForModule(parent.module)

    # for c-ish backends, "main" is already defined, of course
    elif s.name.s == "main":
      let parent = findPendingModule(m, s)
      if parent != nil and sfMainModule in parent.module.flags:
        # but we'll only worry about it for MainModule
        result.add "_"
        result.add getSomeNameForModule(parent.module)

    # something like `default` might need this check
    if (unlikely) result in m.config.cppDefines:
      result.add "_"
      result.add $conflictKey(s)

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

  # critically, we must check for conflicts at the source module
  # in the event a global symbol is actually foreign to `p`
  # NOTE: constants are effectively global
  result = sfGlobal in s.flags or s.kind == skConst

  when p is BProc:
    # if it's nominally proc but has no proc symbol, then we'll use
    # the module scope for conflict resolution; this solves a fun
    # corner-case where we have a toplevel forVar in an inline iterator
    result = result or p.prc.isNil

proc getSetConflict(p: ModuleOrProc; s: PSym): tuple[name: string; counter: int] =
  ## take a backend module or a procedure being generated and produce an
  ## appropriate name and the instances of its occurence, which may be
  ## incremented for this instance
  let m = getem()
  template g(): ModuleGraph = m.g.graph
  var counter = -1         # the current counter for this name
  var next = 1             # the next counter for this name

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
      var parent = findPendingModule(m, s)
      if parent != nil:   # javascript can yield nil here
        when parent is BModule:
          when p is BModule:
            # is it (not) foreign?  terribly expensive, i know.
            if parent.cfilename.string == m.cfilename.string:
              break
          # use or set the existing foreign counter for the key
          (name, counter) = getSetConflict(parent, s)
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
    counter = getOrSet(p.sigConflicts, name, conflictKey(s))
  else:
    # else, stuff it into the local table with the discovered counter
    p.sigConflicts[key] = counter

    # set the next value to the larger of the local and remote values
    p.sigConflicts[name] = max(counter + 1,
                               getOrDefault(p.sigConflicts, name, 1))

  result = (name: name, counter: counter)

proc idOrSig*(m: ModuleOrProc; s: PSym): Rope =
  ## produce a unique identity-or-signature for the given module and symbol
  let conflict = getSetConflict(m, s)
  result = conflict.name.rope
  result.maybeAddCounter conflict.counter
  when false:
    if "setChar" in $result: #startsWith($result, "setChar"):
      debug s
      when m is BModule:
        result = "/*" & $conflictKey(s) & "*/" & result
        debug m.cfilename
        debug "module $4 >> $1 .. $2 -> $3" %
          [ $conflictKey(s), s.name.s, $result, $conflictKey(m.module) ]
      elif m is BProc:
        result = "/*" & $conflictKey(s) & "*/" & result
        debug "  proc $4 >> $1 .. $2 -> $3" %
          [ $conflictKey(s), s.name.s, $result,
           if m.prc != nil: $conflictKey(m.prc) else: "(nil)" ]

proc getTypeName*(p: ModuleOrProc; typ: PType): Rope =
  ## produce a useful name for the given type, obvs
  let m = getem()
  var key = $conflictKey(typ)
  block found:
    # try to find the actual type
    var t = typ
    while true:
      # use an immutable symbol name if we find one
      if t.sym.hasImmutableName:
        # the symbol might need mangling, first
        result = mangleName(p, t.sym)
        break found
      elif t.kind in irrelevantForBackend:
        t = t.lastSon    # continue into more precise types
      else:
        break            # this looks like a good place to stop

    # we'll use the module-level conflicts because, c'mon, it's a type
    assert t != nil
    result = typeName(m, t).rope
    let counter = getOrSet(m.sigConflicts, $result, conflictKey(t))
    result.maybeAddCounter counter
    when false:
      if startsWith($result, "setChar"):
        debug typ
        result.add "/*" & $key & "*/"

  if result == nil:
    internalError(m.config, "getTypeName: " & $typ.kind)

template tempNameForLabel(m: BModule; label: int): string =
  ## create an appropriate temporary name for the given label
  m.tmpBase & $label & "_"

proc hasTempName*(m: BModule; n: PNode): bool {.deprecated: "but why?".} =
  ## true if the module/proc has a temporary cached for the given node
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
  ## create or retrieve a temporary name for the given node; returns
  ## true if a new name was created and false otherwise.  appends the
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
  ## a simpler getTempName that doesn't care where the name comes from
  discard getTempName(m, n, result)

proc getTempName*(m: BModule): Rope =
  ## a factory for making temporary names for use in the backend; this mutates
  ## the module from which the name originates; this always creates a new name
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
    result.add "_0"

proc mangleRecFieldName*(m: BModule; field: PSym): Rope =
  ## Mangle an object field to ensure it is a valid name in the backend.
  if {sfImportc, sfExportc} * field.flags != {}:
    result = field.loc.r
  else:
    result = mangleField(m, field.name).rope
  if result == nil:
    internalError(m.config, field.info, "mangleRecFieldName")

proc assignParam*(p: BProc, s: PSym; ret: PType) =
  ## Push the mangled name into the proc's sigConflicts so that we can
  ## make new local identifiers of the same name without colliding with it.

  # It's likely that the symbol is already in the module scope!
  if s.loc.r == nil or $conflictKey(s) notin p.sigConflicts:
    purgeConflict(p.module, s) # discard any existing counter for this sym
    if s.kind == skResult:
      s.loc.r = ~"result"        # just set it to result if it's skResult
      # record (and verify) the result in the local conflicts table
      if getOrSet(p.sigConflicts, "result", conflictKey(s)) != 0:
        internalError(p.config, s.info, "assignParam: shadowed result")
    else:
      s.loc.r = nil              # critically, destroy the location
      s.loc.r = mangleName(p, s) # then mangle it using the proc scope
  if s.loc.r == nil:
    internalError(p.config, s.info, "assignParam")

proc mangleParamName*(p: BProc; s: PSym): Rope =
  ## mangle a param name when we actually have the target proc
  result = mangleName(p, s)
  if result == nil:
    internalError(p.config, s.info, "mangleParamName")

proc mangleParamName*(m: BModule; s: PSym): Rope =
  ## we should be okay with just a simple mangle here for prototype
  ## purposes; the real meat happens in assignParam later...
  if s.loc.r == nil:
    s.loc.r = mangle(m, s).rope
  result = s.loc.r
  if result == nil:
    internalError(m.config, s.info, "mangleParamName")
