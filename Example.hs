import KBC

zero = Fun "zero" []
add x y = Fun "add" [x, y]
inv x = Fun "-" [x]
a = Var "a"
b = Var "b"
c = Var "c"

axs = [ add zero a :=: a
      , add (inv a) a :=: zero
      , add (add a b) c :=: add a (add b c) ]

main = do
  runProver axs kbc
  return ()
