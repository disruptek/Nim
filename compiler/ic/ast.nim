#[

none of this backend-specific code should exist in ast, but...  here we are.

all this stuff is included into compiler/ast.

]#

when not defined(release):
  var rsets {.compileTime.}: int
  var rgets {.compileTime.}: int

  proc `$`*(loc: TLoc): string =
    result.add "loc[" & $loc.k & "/" & $loc.storage & ": "
    result.add $loc.flags
    result.add "`" & $loc.roap & "`"

proc r*(t: TLoc): Rope =
  ## Capture location queries.
  when not defined(release): inc rgets
  t.roap

proc r*[T](t: var TLoc; m: T): var Rope =
  ## Capture location mutations.
  when T is TLoc:
    {.warning: "potentially unsafe tloc r".}
  result = t.roap
  when not defined(release):
    inc rgets
    inc rsets

proc `r=`*(t: var TLoc; r: Rope) =
  ## Capture location mutations.
  assert r != nil, "use clear(BModule, TLoc)"
  if t.roap != nil:
    when not defined(release):
      if $t.roap != $r:
        echo "changing roap ", cast[uint](t.roap), " from ", $t.r, " to ", $r
        echo "rsets ", rsets, " rgets ", rgets
      inc rsets
  t.roap = r

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
