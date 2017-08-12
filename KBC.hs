{-# LANGUAGE DeriveDataTypeable, Strict #-}
module KBC where

import Debug.Trace

import Data.Generics.Uniplate.Data

import Prelude hiding (lookup)
import Data.Data
import Data.List hiding (lookup, insert)
import Data.Generics.Uniplate.Data
import Data.Map hiding (map, filter, foldr, null, size, (\\))
import qualified Data.Map as M
import Data.Ord
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Except
import Control.Monad.State

type Name = String

data Term = Var !Name
          | Fun !Name !Int ![Term]
          deriving (Eq, Ord, Data, Typeable)

instance Show Term where
  show t = case t of
    Var n -> n
    Fun f _ ts -> f ++ "(" ++ intercalate ", " (show <$> ts) ++ ")"

size :: Term -> Int
size (Var _) = 1
size (Fun _ _ ts) = 1 + sum (size <$> ts)

weight :: Term -> Int
weight (Var _)      = 1
weight (Fun _ w ts) = w + sum (weight <$> ts)

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
      | t == u     -> return subst 
      | occurs a u -> throwError "Occurs check failed"
      | otherwise  -> return $ insert a u subst 
    (_, Var a)     -> unify subst u t
    (Fun a _ ts, Fun b _ us)
      | a == b     -> foldM (uncurry . unify) subst (zip ts us)
      | otherwise  -> throwError "Can not unify different functions"

match :: Subst -> Term -> Term -> Either String Subst
match subst t u = case (t, u) of
  (Var a, u) -> case lookup a subst of
      Just u'
        | u' == u   -> return subst
        | otherwise -> throwError "Pattern match failure"
      Nothing -> return $ insert a u subst
  (Fun a _ ts, Fun b _ us)
    | a == b    -> foldM (uncurry . match) subst (zip ts us)
    | otherwise -> throwError "Pattern match failure"
  _ -> throwError "Pattern match failure"

apply :: Subst -> Term -> Term
apply subst = rewrite go
  where
    go (Var n) = lookup n subst 
    go _       = Nothing

applyMatch :: Subst -> Term -> Term
applyMatch subst = transform go
  where
    go (Var n) = case lookup n subst of
      Just t  -> t
      Nothing -> Var n
    go t = t

occurs :: Name -> Term -> Bool
occurs n t =
  elem n (variables t)

data Equation = !Term :=: !Term deriving (Eq, Ord, Data, Typeable)

instance Show Equation where
  show (lhs :=: rhs) = show lhs ++ " = " ++ show rhs

lhs, rhs :: Equation -> Term
lhs (l :=: _) = l
rhs (_ :=: r) = r

data Rule = !Term :-> !Term deriving (Eq, Ord, Data, Typeable)

instance Show Rule where
  show (lhs :-> rhs) = show lhs ++ " -> " ++ show rhs

rewrites :: Rule -> Term -> [Term]
rewrites (lhs :-> rhs) t = filter (/= t) $ go t
  where
    go t@(Var v) = case match empty lhs t of
      Left _  -> [t]
      Right s -> [t, applyMatch s rhs]
    go t@(Fun f w ts) = case match empty lhs t of
      Left _  -> Fun f w <$> possibilities ts
      Right s -> (applyMatch s rhs) : (Fun f w <$> possibilities ts)

    possibilities [] = [[]]
    possibilities (t:ts) = do
      t'  <- go t
      ts' <- possibilities ts
      return (t' : ts')

fullyRewrite :: Rule -> Term -> Term
fullyRewrite r@(lhs :-> rhs) = go
  where
    go t@(Var v) = case match empty lhs t of
      Left _  -> t
      Right s -> go $ applyMatch s rhs
    go t@(Fun f w ts) = case match empty lhs t of
      Left _  -> Fun f w (go <$> ts)
      Right s -> go $ applyMatch s rhs

type Renamer a = State Int a

runRenamer :: Renamer a -> a
runRenamer r = evalState r 0

gensym :: Int -> String
gensym n
  | n < 26    = letter n
  | otherwise = gensym (n `div` 26) ++ letter (n `mod` 26)
  where
    letter :: Int -> String
    letter n = (:[]) $ ['a'..'z'] !! n

newName :: Renamer Name
newName = do
  i <- get
  modify (+1)
  return $ gensym i 

rename :: Term -> Renamer Term
rename t = do
  let vs = nub $ variables t
  ns <- mapM (\_ -> Var <$> newName) vs
  let subst = fromList $ zip vs ns
  return $ applyMatch subst t

{- Change this to only produce the critical pair arising from rewriting at
 - the specific place -}
superimpose :: Term -> Term -> [Term]
superimpose l r = result
  where
    result = [ apply s lterm | s <- go lterm ]

    (lterm, rterm) = runRenamer $ do
      l <- rename l
      r <- rename r
      return (l, r)

    go (Var v)      = []
    go t@(Fun f _ ts) = case unify empty rterm t of
      Left _  -> concatMap go ts
      Right s -> s : concatMap go ts

-- This function produces way too many redundant rewrites!
allRewrites :: [Rule] -> Term -> [Term]
allRewrites [] t     = []
allRewrites (r:rs) t =
  let rt = rewrites r t
      ar = allRewrites rs t
  in
  ar ++ rt ++ concat [rewrites r t | t <- ar]

criticalPairs :: [Rule] -> Rule -> Rule -> ProofMonad [Equation]
criticalPairs allRules rl@(ll :-> _) rr@(lr :-> _) = do
  let fnub = S.toList . S.fromList
      sups    = fnub $ superimpose ll lr ++ superimpose lr ll
      cps s   = fnub $ allRewrites [rl, rr] s
      cpssups = cps <$> sups

  return $ nub $ filter (not . trivial) $
           map (normalise (rl : rr : allRules)) $
           [ l :=: r | s_cps <- cpssups, l <- s_cps, r <- s_cps ]

axiomToRule :: Equation -> Rule
axiomToRule e
  | trivial e = lhs e :-> rhs e
  | otherwise = let (l :=: r) = order e in
  l :-> r

ruleToAxiom :: Rule -> Equation
ruleToAxiom (l :-> r) = l :=: r

order :: Equation -> Equation
order (l :=: r)
  | weight l < weight r  = r :=: l
  | weight r < weight l  = l :=: r
order ((Var a) :=: r) = r :=: (Var a)
order (l :=: (Var a)) = l :=: (Var a)
order (l@(Fun _ wl _) :=: r@(Fun _ wr _))
  | wl > wr   = r :=: l
  | wl == wr  = case lexLess l r of
    Nothing -> error $ "Non-orientable equation: " ++ show (l :=: r)
    Just b  -> if b then r :=: l else l :=: r
  | otherwise = l :=: r

lexLess :: Term -> Term -> Maybe Bool
lexLess (Var _) (Var _) = Nothing
lexLess (Var _) _       = Just True
lexLess _ (Var _)       = Just False
lexLess (Fun f _ ts) (Fun g _ us)
  | f < g     = Just True
  | g < f     = Just False
  | otherwise = case filter (/= Nothing) $ (uncurry lexLess <$> zip ts us) of
    []          -> Nothing
    (Just a:_) -> Just a

trivial :: Equation -> Bool
trivial (l :=: r) = l == r

normalise :: [Rule] -> Equation -> Equation
normalise rs e = (\e -> if trivial e then e else order e) $
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
                    , rules  :: [Rule]
                    , count  :: Int
                    } deriving (Ord, Eq, Show)

type ProofMonad a = StateT KBCState IO a

runProver :: [Equation] -> ProofMonad () -> IO [Rule]
runProver eqns p = rules <$> execStateT p (KBC eqns [] 0)

reduceRules :: ProofMonad ()
reduceRules = do
  rs <- gets rules
  let rs' = nub
          $ map axiomToRule
          $ filter (not . trivial)
          $ map ((\e -> normalise (rs \\ [axiomToRule e]) e) . ruleToAxiom)
            rs
  modify (\s -> s { rules = rs' })


kbc :: ProofMonad ()
kbc = do
  axs <- gets axioms
  unless (null axs) $ do
    rs <- gets rules
    let ax = normalise rs $ head axs
    modify (\s -> s { axioms = tail $ axioms s })
    unless (trivial ax) $ do
      
      let ar  = axiomToRule ax
      axss <- mapM (criticalPairs (ar:rs) ar) (ar:rs)
      let axs = filter (not . trivial) .
                map (normalise (ar:rs)) $ concat axss
      modify (\s -> s {          -- This needs to be improved somehow
                                 -- take heuristic from JJ Dick paper
                        axioms = sortBy (comparing $ (\e -> weight (lhs e) +
                                                            size (lhs e)))
                               $ axioms s ++ axs
                      , rules = ar : rules s
                      , count = count s + 1
                      })
      c <- gets count
      liftIO $ putStrLn (show c ++ ". " ++ show ar)
    kbc 
