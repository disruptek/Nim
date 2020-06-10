#
#
#           The Nim Compiler
#        (c) Copyright 2012 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module contains the data structures for the C code generation phase.

import

  ast, ropes, options, intsets, sighashes, astalgo, tables, ndi,
  lineinfos, pathutils, modulegraphs, wordrecg, idents

import

  std / [ tables, sets ]

template witness*(body: untyped): untyped {.dirty.} =
  ## perform a dangerous operation on an IC context; ensure it's unsealed!
  assert not m.isSealed
  if not m.isSealed:
    body

template add*(father, son: PNode or PType): untyped {.dirty.} =
  ## perform a dangerous operation on an IC context; ensure it's unsealed!
  witness:
    father.safeAdd son

type
  TLabel* = Rope              # for the C generator a label is just a rope
  TCFileSection* = enum       # the sections a generated C file consists of
    cfsMergeInfo,             # section containing merge information
    cfsHeaders,               # section for C include file headers
    cfsFrameDefines           # section for nim frame macros
    cfsForwardTypes,          # section for C forward typedefs
    cfsTypes,                 # section for C typedefs
    cfsSeqTypes,              # section for sequence types only
                              # this is needed for strange type generation
                              # reasons
    cfsFieldInfo,             # section for field information
    cfsTypeInfo,              # section for type information (ag ABI checks)
    cfsProcHeaders,           # section for C procs prototypes
    cfsData,                  # section for C constant data
    cfsVars,                  # section for C variable declarations
    cfsProcs,                 # section for C procs that are not inline
    cfsInitProc,              # section for the C init proc
    cfsDatInitProc,           # section for the C datInit proc
    cfsTypeInit1,             # section 1 for declarations of type information
    cfsTypeInit2,             # section 2 for init of type information
    cfsTypeInit3,             # section 3 for init of type information
    cfsDebugInit,             # section for init of debug information
    cfsDynLibInit,            # section for init of dynamic library binding
    cfsDynLibDeinit           # section for deinitialization of dynamic
                              # libraries
  TCTypeKind* = enum          # describes the type kind of a C type
    ctVoid, ctChar, ctBool,
    ctInt, ctInt8, ctInt16, ctInt32, ctInt64,
    ctFloat, ctFloat32, ctFloat64, ctFloat128,
    ctUInt, ctUInt8, ctUInt16, ctUInt32, ctUInt64,
    ctArray, ctPtrToArray, ctStruct, ctPtr, ctNimStr, ctNimSeq, ctProc,
    ctCString
  TCFileSections* = array[TCFileSection, Rope] # represents a generated C file
  TCProcSection* = enum       # the sections a generated C proc consists of
    cpsLocals,                # section of local variables for C proc
    cpsInit,                  # section for init of variables for C proc
    cpsStmts                  # section of local statements for C proc
  TCProcSections* = array[TCProcSection, Rope] # represents a generated C proc
  BModule* = ref TCGen
  BProc* = ref TCProc
  TBlock* = object
    id*: int                  # the ID of the label; positive means that it
    label*: Rope              # generated text for the label
                              # nil if label is not used
    sections*: TCProcSections # the code belonging
    isLoop*: bool             # whether block is a loop
    nestedTryStmts*: int16    # how many try statements is it nested into
    nestedExceptStmts*: int16 # how many except statements is it nested into
    frameLen*: int16

  TCProcFlag* = enum
    beforeRetNeeded,
    threadVarAccessed,
    hasCurFramePointer,
    noSafePoints,
    nimErrorFlagAccessed,
    nimErrorFlagDeclared

  ConflictsTable* = TableRef[string, int]

  TCProc = object             # represents C proc that is currently generated
    prc*: PSym                # the Nim proc that this C proc belongs to
    flags*: set[TCProcFlag]
    lastLineInfo*: TLineInfo  # to avoid generating excessive 'nimln' statements
    currLineInfo*: TLineInfo  # AST codegen will make this superfluous
    nestedTryStmts*: seq[tuple[fin: PNode, inExcept: bool, label: Natural]]
                              # in how many nested try statements we are
                              # (the vars must be volatile then)
                              # bool is true when are in the except part of a try block
    finallySafePoints*: seq[Rope]  # For correctly cleaning up exceptions when
                                   # using return in finally statements
    labels*: Natural          # for generating unique labels in the C proc
    blocks*: seq[TBlock]      # nested blocks
    breakIdx*: int            # the block that will be exited
                              # with a regular break
    options*: TOptions        # options that should be used for code
                              # generation; this is the same as prc.options
                              # unless prc == nil
    module*: BModule          # used to prevent excessive parameter passing
    withinLoop*: int          # > 0 if we are within a loop
    splitDecls*: int          # > 0 if we are in some context for C++ that
                              # requires 'T x = T()' to become 'T x; x = T()'
                              # (yes, C++ is weird like that)
    withinTryWithExcept*: int # required for goto based exception handling
    sigConflicts*: ConflictsTable

  TypeCache* = TableRef[SigHash, Rope]
  TypeCacheWithOwner* = Table[SigHash, tuple[str: Rope, owner: PSym]]

  CodegenFlag* = enum
    preventStackTrace,  # true if stack traces need to be prevented
    usesThreadVars,     # true if the module uses a thread var
    frameDeclared,      # hack for ROD support so that we don't declare
                        # a frame var twice in an init proc
    isHeaderFile,       # C source file is the header file
    includesStringh,    # C source file already includes ``<string.h>``
    objHasKidsValid     # whether we can rely on tfObjHasKids

  BModuleList* = ref object of RootObj
    mainModProcs*, mainModInit*, otherModsInit*, mainDatInit*: Rope
    mapping*: Rope             # the generated mapping file (if requested)
    modules*: seq[BModule]     # list of all compiled modules
    modulesClosed*: seq[BModule] # list of the same compiled modules, but in the order they were closed
    forwardedProcs*: seq[PSym] # proc:s that did not yet have a body
    generatedHeader*: BModule  # dark arts
    typeInfoMarker*: TypeCacheWithOwner
    config*: ConfigRef
    graph*: ModuleGraph
    strVersion*, seqVersion*: int # version of the string/seq implementation to use

    nimtv*: Rope            # Nim thread vars; the struct body
    nimtvDeps*: seq[PType]  # type deps: every module needs whole struct
    nimtvDeclared*: IntSet  # so that every var/field exists only once
                            # in the struct
                            # 'nimtv' is incredibly hard to modularize! Best
                            # effort is to store all thread vars in a ROD
                            # section and with their type deps and load them
                            # unconditionally...
                            # nimtvDeps is VERY hard to cache because it's
                            # not a list of IDs nor can it be made to be one.

  TCGen = object of PPassContext # represents a C source file
    s*: TCFileSections        # sections of the C file
    flags*: set[CodegenFlag]  # i think this is for the semaphore impl
    module*: PSym             # the module from whence we came
    filename*: AbsoluteFile   # no idea what this could be
    cfilename*: AbsoluteFile  # filename of the module (including path,
                              # without extension)
    tmpBase*: string          # base for temp identifier generation
    typeCache*: TypeCache     # cache the generated types
    typeABICache*: HashSet[SigHash] # cache for ABI checks; reusing typeCache
                              # would be ideal but for some reason enums
                              # don't seem to get cached so it'd generate
                              # 1 ABI check per occurence in code
    forwTypeCache*: TypeCache # cache for forward declarations of types
    declaredThings*: IntSet   # things we have declared in this .c file
    declaredProtos*: IntSet   # prototypes we have declared in this .c file
    headerFiles*: seq[string] # needed headers to include
    typeInfoMarker*: TypeCache # needed for generating type information
    initProc*: BProc          # code for init procedure
    preInitProc*: BProc       # code executed before the init proc
    hcrCreateTypeInfosProc*: Rope # type info globals are in here when HCR=on
    inHcrInitGuard*: bool     # We are currently within a HCR reloading guard.
    typeStack*: TTypeSeq      # used for type generation
    dataCache*: TNodeTable    # this is where we cache literals in the module
    typeNodes*, nimTypes*: int # used for type info generation
    typeNodesName*, nimTypesName*: Rope # used for type info generation
    labels*: Natural          # for generating unique module-scope names
    extensionLoaders*: array['0'..'9', Rope] # special procs for the
                                             # OpenGL wrapper
    injectStmt*: Rope         # i think this has something to do with iv drugs
    sigConflicts*: ConflictsTable
    g*: BModuleList           # the complete module graph
    ndi*: NdiFile             # "nim debug info" files


    # move all this transform stuff into ic backend?
    transforms*: TransformTable

  TransformKind* = enum
    Unknown
    HeaderFile
    ProtoSet
    ThingSet
    FlagSet
    TypeStack
    Injection
    GraphRope
    InitProc
    PreInit
    Labels
    SetLoc
    LiteralData

  TransformTable* = OrderedTable[SigHash, Transform]

  Transform* = object
    module*: BModule
    case kind*: TransformKind
    of Unknown:
      discard
    of FlagSet:
      flags*: set[CodegenFlag]
    of ProtoSet, ThingSet:
      diff*: IntSet
    of HeaderFile:
      filenames*: seq[string]
    of TypeStack:
      stack*: TTypeSeq
    of Injection:
      rope*: Rope
    of GraphRope:
      field*: string
      grope*: Rope
    of InitProc, PreInit:
      prc*: PSym
    of Labels:
      labels*: int
    of SetLoc:
      nkind*: TNodeKind
      id*: int
      loc*: TLoc
    of LiteralData:
      node*: PNode
      val*: int

template config*(m: BModule): ConfigRef = m.g.config
template config*(p: BProc): ConfigRef = p.module.g.config

proc isNimOrCKeyword*(w: PIdent): bool =
  # Nim and C++ share some keywords
  # it's more efficient to test the whole Nim keywords range
  case w.id
  of ccgKeywordsLow..ccgKeywordsHigh,
     nimKeywordsLow..nimKeywordsHigh,
     ord(wInline): return true
  else: return false

proc includeHeader*(this: BModule; header: string) =
  if not this.headerFiles.contains header:
    this.headerFiles.add header

proc s*(p: BProc, s: TCProcSection): var Rope {.inline.} =
  # section in the current block
  result = p.blocks[^1].sections[s]

proc procSec*(p: BProc, s: TCProcSection): var Rope {.inline.} =
  # top level proc sections
  result = p.blocks[0].sections[s]

proc newProc*(prc: PSym, module: BModule): BProc =
  new(result)
  result.prc = prc
  result.module = module
  result.sigConflicts = newTable[string, int]()
  result.options =
    if prc == nil:
      module.config.options
    else:
      prc.options
  newSeq(result.blocks, 1)
  result.nestedTryStmts = @[]
  result.finallySafePoints = @[]

proc newModuleList*(g: ModuleGraph): BModuleList =
  BModuleList(typeInfoMarker: initTable[SigHash, tuple[str: Rope, owner: PSym]](),
    config: g.config, graph: g, nimtvDeclared: initIntSet())

iterator cgenModules*(g: BModuleList): BModule =
  for m in g.modulesClosed:
    # iterate modules in the order they were closed
    yield m

proc pushType*(m: BModule, typ: PType) =
  for i in 0..high(m.typeStack):
    # pointer equality is good enough here:
    if m.typeStack[i] == typ: return
  m.typeStack.add(typ)

proc newPreInitProc*(m: BModule): BProc =
  result = newProc(nil, m)
  # little hack so that unique temporaries are generated:
  result.labels = 100_000

proc initProcOptions*(m: BModule): TOptions =
  let opts = m.config.options
  if sfSystemModule in m.module.flags: opts-{optStackTrace} else: opts
