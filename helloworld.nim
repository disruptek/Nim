import strutils
import json
import hashes
import terminal
import tables
import pegs
import httpclient
import strformat
import sets

when true:
  echo "hellop world".endsWith "d"
  #echo newJString("hello").getStr == "hello"
  echo "hello world"
  #echo isatty(stdin)
  #echo hash("")
  #echo &"goats"
else:
  proc unused() =
    discard "goats"

  proc hellow() =
    echo "hello world"

  hellow()
