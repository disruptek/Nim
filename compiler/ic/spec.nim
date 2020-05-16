## This module implements the new compilation cache.
import

  ".." / [ ast, cgendata, sighashes, modulegraphs, ropes, somenode ]

import

  std / [ os, tables, deques ]


include

  # so we can see the icCache
  pcontext

type
  CacheStrategy* = enum
    Reads       = "📖"
    Writes      = "✒️"
    Immutable   = "🔏"

  CacheableObject* = PSym or PNode or PType

  State* = enum
    Invalid     = -1
    Initialize
    Load
    Generate
    Store
    Merge
    Abort
    Done

  CacheUnitKind* = enum Symbol, Node, Type

  # the in-memory representation of a cachable unit of backend codegen
  CacheUnit*[T: CacheableObject] = object
    strategy*: set[CacheStrategy]
    kind*: CacheUnitKind
    node*: T                     # the node itself
    snippets*: SnippetTable      # snippets for this node
    transforms*: TransformTable  # transforms for this node
    graph*: ModuleGraph          # the original module graph
    modules*: BModuleList        # modules being built by the backend
    origin*: BModule             # presumed original module
    state*: State                # future state of cache unit
    initialized*: bool           # it's fully-alloc'd and must be torn down

  # the in-memory representation of the database record
  Snippet* = object
    signature*: SigHash       # we use the signature to associate the node
    module*: BModule          # the module to which the snippet applies
    section*: TCFileSection   # the section of the module in which to write
    code*: Rope               # the raw backend code itself, eg. C/JS/etc.

  SnippetTable* = OrderedTable[SigHash, Snippet]
  Snippets* = seq[Snippet]

const
  nimIcAudit* = when not defined(release): true else: false
when nimIcAudit:
  import audit
  export audit

# safen unsafe ast adds
export add

proc isSealed*(c: PContext): bool = c.icSealed

proc isValid(c: PContext; n: SomeNode): bool  =
  assert c.module != nil
  if c.module != nil:
    assert not n.isNil
    block:
      case n.kind
      of nkNone:
        discard
      else:
        let m = getModule(n)
        if m == nil:
          assert false, $n.kind & " node lacks module"
        else:
          if c.module != getModule(n):
            break
      result = n.isValid

proc addIcCache*(c: PContext; p: PNode | PSym | PType) =
  ## add the given node to the context's cache
  let value = newSomeNode(p)
  # an assert for now
  assert c.isValid(value) # if c.isValid(value):
  c.icCache.addLast value

iterator consumer*(c: PContext): SomeNode =
  assert not c.isSealed
  if c.isSealed:
    raise newException(Defect, "context already sealed")
  c.icSealed = true
  try:
    while not c.icCache.isEmpty:
      let
        node = c.icCache.popFirst
      case node.kind
      of nkType:
        node.typ.icSealed = true
      else:
        discard
  finally:
    assert c.icCache.isEmpty

proc `$`*(m: BModule): string =
  result = $m.module.id & ".." & splitFile(m.cfilename.string).name

template mutateLocation*(p: PSym or PType; body: untyped): untyped
  {.deprecated: "mutation of psym/ptype without module".} =
  var loc {.inject.}: TLoc = p.loc
  body
  if loc != p.loc:
    p.setLocation(loc)

template `[]=`*(ops: var TAttachedOps; i: TTypeAttachedOp; p: PSym) {.dirty.} =
  witness:
    system.`[]=`(ops, i, p)

proc `[]`*(ops: TAttachedOps; i: TTypeAttachedOp): PSym =
  result = system.`[]`(ops, i)
