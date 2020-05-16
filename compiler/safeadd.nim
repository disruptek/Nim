import ast, ic

proc add*(father, son: PNode) =
  ## perform a dangerous operation on a node; assume it's unsealed!
  father.safeAdd son
