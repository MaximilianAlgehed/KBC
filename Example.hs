import KBC

-- TODO: Find a method for computing these weights!
zero = Fun "zero" 1 []
one  = Fun "one"  2 []
add x y = Fun "add" 3 [x, y]
mul x y = Fun "mul" 4 [x, y]
inv x = Fun "-" 0 [x]
a = Var "a"
b = Var "b"
c = Var "c"

axs = [ add zero a :=: a
      , add (inv a) a :=: zero
      , add (add a b) c :=: add a (add b c)
      --, mul one a :=: a
      --, mul a one :=: a
      --, mul (mul a b) c :=: mul a (mul b c)
      {-, mul a (add b c) :=: add (mul a b) (mul a c)-}]

main = do
  runProver axs kbc
  return ()
