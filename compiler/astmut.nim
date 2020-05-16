type
  Indexable = PNode or PType

  TreeRead* = object
  TreeWrite* = object
  TreeBreak* = object    # used to break compilation
  TreeSafe* = object     # an unsafe mutation is marked safe.  i know.

# we have to deal with these at some point, too
#
template `[]`*(n: Indexable, i: int): Indexable = n.sons[i]
template `[]=`*(n: Indexable, i: int; x: Indexable) = n.sons[i] = x

template `[]`*(n: Indexable, i: BackwardsIndex): Indexable = n[n.len - i.int]
template `[]=`*(n: Indexable, i: BackwardsIndex; x: Indexable) = n[n.len - i.int] = x

proc unsafeAdd(father, son: Indexable) =
  ## an unsafe add that we want to permit
  assert son != nil
  when not defined(nimNoNilSeqs):
    if father.sons == nil:
      father.sons = @[]
  father.sons.add son

proc safeAdd*(father, son: Indexable) =
  ## ultimately, this should be safe.  it's not, at the moment.
  father.unsafeAdd son

template add(father, son: PNode or PType) =
  ## used in astnim
  father.safeAdd son

proc r*(a: TLoc): Rope {.tags: [TreeRead].} =
  ## read-only interface to location rope
  result = a.roap

proc loc*(p: PSym or PType): TLoc {.tags: [TreeRead].} =
  ## read-only interface to location
  result = p.location

proc mloc(p: PSym or PType): var TLoc
  {.tags: [TreeRead, TreeWrite], deprecated: "use a witness".} =
  ## used in ast.nim for assignType()
  result = p.location
  when defined(debugTLoc):
    echo "mut loc"

proc setLocation*(p: PSym or PType; a: TLoc) {.tags: [TreeRead, TreeWrite, TreeSafe].} =
  ## this should be run almost nowhere
  p.location = a

proc clearRope*(a: TLoc) {.tags: [TreeWrite].} =
  ## a safe noop
  assert a.roap == nil
  when defined(debugTLoc):
    echo "clear imm"

proc clearRope*(a: var TLoc) {.tags: [TreeWrite].} =
  ## an unsafe empty of the roap
  a.roap = nil
  when defined(debugTLoc):
    echo "clear mut"

# used in ic because dumb
proc setRopeSecret*(a: var TLoc; roap: Rope) {.tags: [TreeWrite].} =
  a.roap = roap

# used in ic because dumb
proc setRopeSecret*(a: var TLoc; s: string) {.tags: [TreeWrite].} =
  a.roap = rope(s)

proc setRope(a: TLoc; roap: Rope) {.tags: [TreeWrite].} =
  ## a trap to catch bad attempts to mutate an immutable
  assert roap == nil, "attempt to mutate an immutable with nil"
  assert a.roap == nil, "attempt to mutate an immutable loc.rope"
  when defined(debugTLoc):
    echo "set rope imm"

proc setRope*(a: var TLoc; roap: Rope) {.tags: [TreeWrite].} =
  ## set a location rope using a rope; pretty dangerous stuff!
  assert roap != nil, "attempt to mutate with nil"
  a.roap = roap
  when defined(debugTLoc):
    echo "set rope mut"

proc setRope*(a: var TLoc; s: string) =
  ## set a location rope using a string; strings are the future!
  a.setRope rope(s)

proc isEmpty*(a: TLoc): bool =
  ## true if the TLoc appears uninitialized
  block:
    if a.roap != nil: break
    if a.lode != nil: break
    if a.k != TLocKind.low: break
    if a.storage != TStorageLoc.low: break
    if a.flags != {}: break
    result = true
    assert a == default(TLoc)

proc mergeLoc(a: var TLoc; b: TLoc) {.tags: [TreeRead, TreeWrite].} =
  when defined(debugTLoc):
    echo "mut merge"
  if a.k == locNone:
    assert a.k == low(a.k)
    a.k = b.k
  if a.storage == OnUnknown:
    assert a.storage == low(a.storage)
    a.storage = b.storage
  a.flags = a.flags + b.flags
  if a.lode == nil:
    a.lode = b.lode
  if a.r == nil:
    if b.r == nil:
      a.clearRope
    else:
      a.setRope(b.r)
