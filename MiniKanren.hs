{-# LANGUAGE DeriveFunctor #-}

module MiniKanren where

import qualified Data.Set as Set

import Data.List (intercalate, deleteBy)
import Control.Applicative (Alternative(..))
import Control.Monad (foldM, ap, MonadPlus(..))
import Data.Foldable (foldl')

--
-- Stream definition
--
infixr 3 :::

data Stream a = Nil | a ::: Stream a | Suspend (Stream a)
  deriving (Eq, Show)

instance Functor Stream where
  fmap _ Nil = Nil
  fmap f (a ::: as) = f a ::: fmap f as
  fmap f (Suspend as) = Suspend (fmap f as)

instance Applicative Stream where
  pure a = a ::: Nil

  (<*>) = error "?"

instance Alternative Stream where
  empty = Nil
  (<|>) = mplus

instance Monad Stream where
  return = pure

  Nil       >>= f = Nil
  a ::: as  >>= f = f a `mplus` (as >>= f)
  Suspend s >>= f = Suspend (s >>= f)

instance MonadPlus Stream where
  mzero = Nil

  Nil         `mplus` x = x
  (a ::: as)  `mplus` x = a ::: x `mplus` as
  (Suspend f) `mplus` x = x `mplus` f

sToList Nil = []
sToList (a ::: as) = a : sToList as
sToList (Suspend as) = sToList as

--
-- Syntax
--

data PreTerm a =
    Var String              -- | Syntax variable
  | Idx a                   -- | Semantic variable
  | Ctr String [PreTerm a]  -- | Contructor
  deriving (Eq, Functor)

instance Applicative PreTerm where
  pure = Idx
  (<*>) = ap

-- | A monad for terms is a substitution.
-- | We substitute only semantic variables.
instance Monad PreTerm where
  return = pure

  (Idx a)    >>= f = f a
  (Ctr n ts) >>= f = Ctr n ((>>= f) <$> ts)
  (Var a)    >>= _ = (Var a)

type Term = PreTerm Int

infix 4 :=:
infixr 3 :&:
infixr 3 :|:

data Expr =
    Fresh [String] Expr
  | Term :=: Term
  | Expr :&: Expr
  | Expr :|: Expr
  | Call String [Term]
  deriving Eq

data Def = Def { dfName :: String, dfArgs :: [String], dfBody :: Expr}

newtype Program = Program [(String, Def)]

type Goal = Expr

type Subst = [(Int, Term)]

data Env = Env { envSubst :: Subst, envFreeVar :: Int }
  deriving Show

succFreeVar :: Env -> Env
succFreeVar (Env s i) = Env s (succ i)

type SemanticVar = Int

--
-- Unification
--
insert :: Subst -> SemanticVar -> Term -> Maybe Subst
insert s n t
  | t' == Just t = Just s
  | Nothing <- t' = Just $ (n, t) : s
  | otherwise = Nothing
  where t' = lookup n s

unionSubst :: Subst -> Subst -> Maybe Subst
unionSubst = foldM (uncurry . insert)

freeVars :: Term -> Set.Set SemanticVar
freeVars (Idx i) = Set.singleton i
freeVars (Var _) = Set.empty
freeVars (Ctr _ args) = Set.unions (freeVars <$> args)

walk :: Subst -> Term -> Term
walk s (Idx n)
 | Just t' <- lookup n s
 = walk s t'
walk _ t = t

unify :: Subst -> Term -> Term -> Maybe Subst
unify s t1 t2 = unify' s (walk s t1) (walk s t2)

unify' :: Subst -> Term -> Term -> Maybe Subst
unify' s (Idx a) (Idx b)
  | a == b
  = Just s
unify' s (Idx a) t
  | a `notElem` freeVars t
  = insert s a t
unify' s t (Idx a)
  | a `notElem` freeVars t
  = insert s a t
unify' s (Ctr n1 a1) (Ctr n2 a2)
  | n1 == n2
  , length a1 == length a2
  = unifyList s a1 a2
unify' _ _ _
  = Nothing

unifyList s [] [] = Just s
unifyList _ [] _  = Nothing
unifyList _ _ [] = Nothing
unifyList s (x:xs) (y:ys) =
  do
    s'  <- unify s x y
    let xs' = applySubstToTerms s' xs
    let ys' = applySubstToTerms s' ys
    s'' <- unifyList s xs' ys'
    unionSubst s' s''

applySubstToTerms :: Subst -> [Term] -> [Term]
applySubstToTerms s ts = [applySubstToTerm s t | t <- ts]

applySubstToTerm :: Subst -> Term -> Term
applySubstToTerm s t = t >>= (\v -> maybe (Idx v) (applySubstToTerm s) (v `lookup` s))

applySubstToExpr :: Subst -> Expr -> Expr
applySubstToExpr s (e1 :&: e2)  = applySubstToExpr s e1 :&: applySubstToExpr s e2
applySubstToExpr s (e1 :|: e2)  = applySubstToExpr s e1 :|: applySubstToExpr s e2
applySubstToExpr s (Fresh as e) = Fresh as (applySubstToExpr s e)
applySubstToExpr s (Call n ts)  = Call n (applySubstToTerms s ts)
applySubstToExpr s (t1 :=: t2)  = applySubstToTerm s t1 :=: applySubstToTerm s t2

--
-- Run
--
eval :: Program -> Env -> Expr -> Stream Env
eval = go
  where
    go prg env (Fresh fs e) = uncurry (go prg) $ foldl' evalFresh (env, e) fs
    go prg env (t1 :=: t2) = equiv env t1 t2
    go prg env (e1 :&: e2) = go prg env e1 >>= (\k -> go prg k e2)
    go prg env (e1 :|: e2) = go prg env e1 `mplus` go prg env e2
    go prg@(Program def) env (Call name args)
      | Just (Def name params body) <- lookup name def
      , length params == length args
      = uncurry (go prg) $ foldl' evalCall  (env, body) $ zip params args
      | otherwise
      = error $ "Call: no definition for <" ++ name ++ ">(" ++ show args ++ ")"

    evalFresh (env, e) f = (succFreeVar env, substituteSyntaxVar f (envFreeVar env) e)
    evalCall x@(env, expr) (param, arg) = applySubstToExpr [(envFreeVar env, arg)] <$> evalFresh x param

    equiv :: Env -> Term -> Term -> Stream Env
    equiv (Env subst i) t1 t2
      | Just subst' <- unify subst t1 t2
      = (Env subst' i) ::: Nil
    equiv _ _ _ = Nil

substituteSyntaxVar :: String -> SemanticVar -> Expr -> Expr
substituteSyntaxVar = go
  where
    go n i (t1 :=: t2) = f n i t1 :=: f n i t2

    go n i (e1 :&: e2) = go n i e1 :&: go n i e2
    go n i (e1 :|: e2) = go n i e1 :|: go n i e2
    go n i t@(Fresh fs e) | n `elem` fs = t
                          | otherwise   = Fresh fs (go n i e)
    go n i (Call nm ts) = Call nm (f n i <$> ts)

    f n i (Var n') | n == n' = Idx i
    f n i (Ctr nm ts) = Ctr nm (f n i <$> ts)
    f _ _ t = t

--
-- Pretty Printing
--
instance (Show a) => Show (PreTerm a) where
  show (Var s) = s
  show (Idx i) = "_" ++ show i
  show (Ctr name ts) = '`' : name ++ "(" ++ intercalate ", " (show <$> ts) ++ ")"

instance Show Expr where
  show (Fresh fs expr) = "fresh (" ++ intercalate ", " fs ++ ") " ++ show expr
  show (t1 :=: t2) = show t1 ++ " :=: " ++ show t2
  show (e1 :&: e2) = "(" ++ show e1 ++ ") :&: (" ++ show e2 ++ ")"
  show (e1 :|: e2) = "(" ++ show e1 ++ ") :|: (" ++ show e2 ++ ")"
  show (Call name ts) = name ++ "(" ++ intercalate ", " (show <$> ts) ++ ")"

instance Show Def where
  show (Def name args body) = name ++ "(" ++ intercalate ", " args ++ ") = " ++ show body

instance Show Program where
  show (Program ds) = intercalate "\n" ((show . snd) <$> ds)

--
-- Examples
--
nil = Ctr "nil" []
cons x y = Ctr "cons" [x, y]

zero = Ctr "zero" []
suc x = Ctr "suc" [x]

one = suc zero
two = suc one

append = Program [("append", app)]
  where
    app = Def "append" ["X", "Y", "R"] $
              (Var "X" :=: nil :&: Var "Y" :=: Var "R")
          :|: Fresh ["H", "T", "TY"]
                (Var "X" :=: cons (Var "H") (Var "T") :&:
                 Var "R" :=: cons (Var "H") (Var "TY") :&:
                 Call "append" [Var "T", Var "Y", Var "TY"])

query1 :: Goal
query1 = Fresh ["A"] $ Call "append" [cons zero nil, Var "A", cons zero $ cons one $ nil]

query2 :: Goal
query2 = Fresh ["A"] $ Call "append" [cons zero nil, cons one nil, cons zero $ cons one $ nil]

query3 :: Goal
query3 = Fresh ["A", "B"] $ Call "append" [Var "A", Var "B", cons zero $ cons one $ nil]

query4 :: Goal
query4 = Fresh ["A", "B", "C"] $ Call "append" [Var "A", Var "B", Var "C"]

env0 = Env [] 0
