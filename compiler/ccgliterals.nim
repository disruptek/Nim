#
#
#           The Nim Compiler
#        (c) Copyright 2018 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from cgen.nim

## This include file contains the logic to produce constant string
## and seq literals. The code here is responsible that
## ``const x = ["a", "b"]`` works without hidden runtime creation code.
## The price is that seqs and strings are not purely a library
## implementation.

template detectVersion(field, corename) =
  if m.g.field == 0:
    let core = getCompilerProc(m.g.graph, corename)
    if core == nil or core.kind != skConst:
      m.g.field = 1
    else:
      m.g.field = toInt(ast.getInt(core.ast))
  result = m.g.field

proc detectStrVersion(m: BModule): int =
  detectVersion(strVersion, "nimStrVersion")

proc detectSeqVersion(m: BModule): int =
  detectVersion(seqVersion, "nimSeqVersion")

# ----- Version 1: GC'ed strings and seqs --------------------------------

proc genStringLiteralDataOnlyV1(m: BModule, s: string; name: Rope) =
  discard cgsym(m, "TGenericSeq")
  m.s[cfsData].addf("STRING_LITERAL($1, $2, $3);$n",
                    [name, makeCString(s), rope(s.len)])

proc genStringLiteralDataOnlyV1(m: BModule, s: string): Rope =
  result = getTempName(m)
  genStringLiteralDataOnlyV1(m, s, result)

proc genStringLiteralV1(m: BModule; n: PNode): Rope =
  if s.isNil:
    result = ropecg(m, "((#NimStringDesc*) NIM_NIL)", [])
  else:
    var name: Rope
    if m.getTempName(n, name):
      genStringLiteralDataOnlyV1(m, n.strVal, name)
    result = ropecg(m, "((#NimStringDesc*) &$1)", [name])

# ------ Version 2: destructor based strings and seqs -----------------------

proc genStringLiteralDataOnlyV2(m: BModule, s: string; result: Rope; isConst: bool) =
  let constr = if isConst: rope"const" else: rope""
  m.s[cfsData].addf("static $4 struct {$n" &
       "  NI cap; NIM_CHAR data[$2+1];$n" &
       "} $1 = { $2 | NIM_STRLIT_FLAG, $3 };$n",
       [result, rope(s.len), makeCString(s), constr])

proc genStringLiteralV2(m: BModule; n: PNode; isConst: bool): Rope =
  const
    codegenf = "static $4 NimStringV2 $1 = {$2, (NimStrPayload*)&$3};$n"
  let constr = if isConst: rope"const" else: rope""
  var name: Rope

  # this is a little subtle due to ..DataOnly.. side-effects

  if m.getTempName(n, name):
    genStringLiteralDataOnlyV2(m, n.strVal, name, isConst)
    result = getTempName(m)
    discard cgsym(m, "NimStrPayload")
    discard cgsym(m, "NimStringV2")
  else:
    result = getTempName(m)
  m.s[cfsData].addf(codegenf,
                    [result, rope(n.strVal.len), name, constr])

proc genStringLiteralV2Const(m: BModule; n: PNode; isConst: bool): Rope =
  var name: Rope
  if m.getTempName(n, name):
    discard cgsym(m, "NimStrPayload")
    discard cgsym(m, "NimStringV2")
    # string literal not found in the cache:
    genStringLiteralDataOnlyV2(m, n.strVal, name, isConst)
  result = "{$1, (NimStrPayload*)&$2}" % [rope(n.strVal.len), name]

# ------ Version selector ---------------------------------------------------

proc genStringLiteralDataOnly(m: BModule; s: string; info: TLineInfo;
                              isConst: bool): Rope =
  case detectStrVersion(m)
  of 0, 1: result = genStringLiteralDataOnlyV1(m, s)
  of 2:
    result = getTempName(m)
    genStringLiteralDataOnlyV2(m, s, result, isConst)
  else:
    localError(m.config, info, "cannot determine how to produce code for string literal")

proc genNilStringLiteral(m: BModule; info: TLineInfo): Rope =
  result = ropecg(m, "((#NimStringDesc*) NIM_NIL)", [])

proc genStringLiteral(m: BModule; n: PNode): Rope =
  case detectStrVersion(m)
  of 0, 1: result = genStringLiteralV1(m, n)
  of 2: result = genStringLiteralV2(m, n, isConst = true)
  else:
    localError(m.config, n.info, "cannot determine how to produce code for string literal")
