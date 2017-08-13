import KBC

-- TODO: Find a method for computing these weights!
nil = Fun "nil" 0 []
cons x xs = Fun "cons" 2 [x, xs]
xs +++ ys = Fun "append" 1 [xs, ys]
x  = Var "x"
xs = Var "xs"
ys = Var "ys"

-- Do the induction
stepXS = Fun "XS" 0 []
baseCase = nil +++ nil :=: nil
stepCase = (cons x stepXS) +++ nil :=: (cons x stepXS) 

axs = [ nil +++ xs :=: xs
      , (cons x xs) +++ ys :=: cons x (xs +++ ys)
      , stepXS +++ nil :=: stepXS ]

main = do
  rules <- runProver axs kbc
  print $ normalise rules baseCase
  print $ normalise rules stepCase 
  return ()
