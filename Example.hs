import KBC

-- TODO: Find a method for computing these weights!
zero = Fun "zero" 1 []
add x y = Fun "add" 2 [x, y]
inv x = Fun "-" 0 [x]
a = Var "a"
b = Var "b"
c = Var "c"

axs = [ add zero a :=: a
      , add (inv a) a :=: zero
      , add (add a b) c :=: add a (add b c) ]

main = do
  runProver axs kbc
  return ()
