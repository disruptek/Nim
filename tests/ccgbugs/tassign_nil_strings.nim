discard """
  cmd: "nim $target --nilseqs:off $options $file"
  output: "Hello"
  ccodecheck: "\\i@'a_ = ((NimStringDesc*) NIM_NIL)'"
"""

proc main() =
  var a = "Hello"
  echo a
  a = ""
  doAssert a.len == 0

main()
