import macros
#[

none of this backend-specific code should exist in ast, but...  here we are.

all this stuff is included into compiler/ast.

]#

when not defined(release):
  proc `$`*(loc: TLoc): string =
    result.add "loc[" & $loc.k & "/" & $loc.storage & ": "
    result.add $loc.flags
    result.add "`" & $loc.roap & "`"

proc r*(t: TLoc): Rope =
  ## Capture location queries.
  t.roap

proc r*[T](t: var TLoc; m: T): var Rope =
  ## Capture location mutations.
  when T is TLoc:
    {.warning: "potentially unsafe tloc r".}
  result = t.roap

macro `r=`*(t: var TLoc; r: Rope) =
  ## Capture location mutations.
  if r.kind == nnkNilLit:
    error "use clear(TLoc, Witness)"
  result = newAssignment(newDotExpr(t, ident"roap"), r)

proc clear*[T](t: var TLoc; m: T) =
  ## Empty a location rope safely.
  when T is TLoc:
    assert t.roap == nil
    {.warning: "potentially unsafe tloc clear".}
  t.roap = nil

proc clearLoc*[T](p: PSym or PType; m: T) =
  ## Empty a location rope safely with `m` as the witness.
  clear(p.loc, m)

proc initLoc*[T](m: T; result: var TLoc, k: TLocKind, lode: PNode, s: TStorageLoc) =
  ## Initialization for TLoc objects.
  result.k = k
  result.storage = s
  result.lode = lode
  result.clear m
  result.flags = {}

proc mergeLoc(a: var TLoc, b: TLoc) =
  if a.k == low(a.k): a.k = b.k
  if a.storage == low(a.storage): a.storage = b.storage
  a.flags.incl b.flags
  if a.lode == nil: a.lode = b.lode
  # XXX: cheating for now
  if a.roap == nil: a.roap = b.r
