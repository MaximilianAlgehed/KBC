{-# LANGUAGE DeriveDataTypeable #-}
module KBC where

import Data.Generics.Uniplate.Data

import Prelude hiding (lookup)
import Data.Data
import Data.List hiding (lookup, insert)
import Data.Generics.Uniplate.Data
import Data.Map hiding (map, filter, foldr, null)
import qualified Data.Map as M
import Data.Ord

import Control.Monad
import Control.Monad.Except
import Control.Monad.State

type Name = String

data Term = Var Name
          | Fun Name [Term]
          deriving (Eq, Data, Typeable)

instance Show Term where
  show t = case t of
    Var n -> n
    Fun f ts -> f ++ "(" ++ intercalate ", " (show <$> ts) ++ ")"

instance Ord Term where
  compare = comparing weight

weight :: Term -> Int
weight (Var _)    = 1
weight (Fun _ []) = 0
weight (Fun _ ts) = 2 + sum (weight <$> ts)

replace :: Data t => Term -> Term -> t -> t 
replace u1 u2 = transformBi go
  where
    go t = if t == u1 then u2 else t

variables :: Data t => t -> [Name]
variables a = nub [ n | Var n <- universeBi a ]

type Subst = Map Name Term

unify :: Subst -> Term -> Term -> Either String Subst 
unify subst tin uin = let (t, u) = (apply subst tin, apply subst uin) in
  case (t, u) of
    (Var a, u)
      | t == u                   -> return subst 
      | occurs a (apply subst u) -> throwError "Occurs check failed"
      | otherwise                -> return $ insert a u subst 
    (_, Var a)                   -> unify subst u t
    (Fun a ts, Fun b us)
      | a == b    -> foldM (uncurry . unify) subst (zip ts us)
      | otherwise -> throwError "Can not unify different functions"

match :: Subst -> Term -> Term -> Either String Subst
match subst t u = case (t, u) of
  (Var a, u) -> case lookup a subst of
      Just u'
        | u' == u   -> return subst
        | otherwise -> throwError "Pattern match failure"
      Nothing -> return $ insert a u subst
  (Fun a ts, Fun b us)
    | a == b    -> foldM (uncurry . match) subst (zip ts us)
    | otherwise -> throwError "Pattern match failure"
  _ -> throwError "Pattern match failure"

apply :: Data t => Subst -> t -> t 
apply subst = rewriteBi go
  where
    go (Var n) = lookup n subst 
    go _       = Nothing

occurs :: Name -> Term -> Bool
occurs n t =
  elem n (variables t)

data Equation = Term :=: Term deriving (Eq, Ord, Data, Typeable)

instance Show Equation where
  show (lhs :=: rhs) = show lhs ++ " = " ++ show rhs

data Rule = Term :-> Term deriving (Eq, Ord, Data, Typeable)

instance Show Rule where
  show (lhs :-> rhs) = show lhs ++ " -> " ++ show rhs

rewrites :: Rule -> Term -> [Term]
rewrites (lhs :-> rhs) t = filter (/= t) . nub . go $ t
  where
    go t@(Var v) = case match empty lhs (Var v) of
      Left _  -> [t]
      Right s -> [t, apply s rhs]
    go t@(Fun f ts) = case match empty lhs t of
      Left _  -> Fun f <$> possibilities ts
      Right s -> (apply s rhs) : (Fun f <$> possibilities ts)

    possibilities [] = [[]]
    possibilities (t:ts) = do
      t' <- go t
      ts' <- possibilities ts
      return (t' : ts')

allRewrites :: [Rule] -> Term -> [Term]
allRewrites [] t     = [t]
allRewrites (r:rs) t =
  let fr  = fullyRewrite r t
      ros = rewrites r t in
  fr : allRewrites rs fr ++
  concatMap (allRewrites (r:rs)) ros ++
  allRewrites rs t

fullyRewrite :: Rule -> Term -> Term
fullyRewrite (lhs :-> rhs) = rewrite go
  where
    go t = case match empty lhs t of
      Left _  -> Nothing
      Right s -> Just $ apply s rhs

type Renamer a = State Int a

runRenamer :: Renamer a -> a
runRenamer r = evalState r 0

newName :: Renamer Name
newName = do
  i <- get
  modify (+1)
  return $ "?a" ++ show i

rename :: Term -> Renamer Term
rename t = do
  let vs = nub $ variables t
  ns <- mapM (\_ -> Var <$> newName) vs
  let subst = fromList $ zip vs ns
  return $ apply subst t

superimpose :: Term -> Term -> [Term]
superimpose l r = [ apply s lterm | s <- go lterm ]
  where
    (lterm, rterm) = runRenamer $ do
      l <- rename l
      r <- rename r
      return (l, r)

    go (Var v)      = []
    go t@(Fun f ts) = case unify empty rterm t of
      Left _  -> concatMap go ts
      Right s -> s : concatMap go ts

criticalPairs :: [Rule] -> Rule -> Rule -> [Equation]
criticalPairs allRules rl@(ll :-> _) rr@(lr :-> _) =
  let sups  = superimpose ll lr ++ superimpose lr ll
      cps s = allRewrites [rl, rr] s in
  nub $ filter (not . trivial) $ map (normalise (rl : rr : allRules)) $
  nub $ [ l :=: r | s <- sups, l <- cps s, r <- cps s, l /= r ]

axiomToRule :: Equation -> Rule
axiomToRule e = let (l :=: r) = order e in
  l :-> r

order :: Equation -> Equation
order (l :=: r)
  | l < r     = r :=: l
  | otherwise = l :=: r

trivial :: Equation -> Bool
trivial (l :=: r) = l == r

normalise :: [Rule] -> Equation -> Equation
normalise rs e = order $
  converge
    (\e ->
      foldr (\rule (l :=: r) ->
        (fullyRewrite rule l) :=: (fullyRewrite rule r)) e rs) e
  where
    converge op t = let ot = op t in
      if ot == t then
        ot
      else
        converge op ot

data KBCState = KBC { axioms :: [Equation]
                    , rules  :: [Rule] } deriving (Ord, Eq, Show)

type ProofMonad a = StateT KBCState IO ()

runProver :: [Equation] -> ProofMonad () -> IO [Rule]
runProver eqns p = rules <$> execStateT p (KBC eqns [])

kbc :: ProofMonad ()
kbc = do
  axs <- gets axioms
  unless (null axs) $ do
    rs <- gets rules
    let ax = normalise rs $ head axs
    modify (\s -> s { axioms = tail $ axioms s })
    unless (trivial ax) $ do
      let ar  = axiomToRule ax
          axs = concatMap (criticalPairs (ar:rs) ar) (ar:rs)
      liftIO $ print ar
      modify (\s -> s { axioms = axioms s ++ axs, rules = ar : rules s })
    kbc 
