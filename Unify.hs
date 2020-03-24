{-# LANGUAGE DeriveFunctor #-}
module Unify where

import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Control.Monad (foldM, ap)

type Name = String

data PreTerm a =
    Var { var :: a}
  | Func { name :: Name, args :: [PreTerm a] }
  deriving (Show, Functor, Eq)

instance Applicative PreTerm where
  pure = Var
  (<*>) = ap

instance Monad PreTerm where
  return = pure
  (Var a) >>= f = f a
  (Func n ts) >>= f = Func n ((>>= f) <$> ts)

type Term = PreTerm String

type Subst = [(Name, Term)]

insert :: Subst -> String -> Term -> Maybe Subst
insert s n t
  | t' == Just t = Just s
  | Nothing <- t' = Just $ (n, t) : s
  | otherwise = Nothing
  where t' = lookup n s

unionSubst :: Subst -> Subst -> Maybe Subst
unionSubst = foldM (uncurry . insert)

freeVars :: Term -> Set.Set String
freeVars (Var x) = Set.singleton x
freeVars (Func _ args) = Set.unions (freeVars <$> args)

unify :: Subst -> Term -> Term -> Maybe Subst
unify s t1 t2 = unify' s (walk s t1) (walk s t2)
  where
    walk :: Subst -> Term -> Term
    walk s (Var n)
     | Just t' <- lookup n s
     = walk s t'
    walk _ t = t

    unify' :: Subst -> Term -> Term -> Maybe Subst
    unify' s (Var a) (Var b)
      | a == b
      = Just s
    unify' s (Var a) t
      | a `notElem` freeVars t
      = insert s a t
    unify' s t (Var a)
      | a `notElem` freeVars t
      = insert s a t
    unify' s (Func n1 a1) (Func n2 a2)
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
    applySubstToTerm s t = t >>= (\v -> maybe (Var v) (applySubstToTerm s) (v `lookup` s))

test msg t1 t2 = do
  putStrLn $ ">>>" ++ msg
  let s = unify [] t1 t2
  putStrLn $ "Result: " ++ show s

test1 = test "Ok: x == y" (Var "x") (Var "y")
test2 = test "Ok: x == x" (Var "x") (Var "x")
test3 = test "Ok: x == f()" (Var "x") (Func "f" [])
test4 = test "Fail: g(x) == x" (Func "g" [Var "x"]) (Var "x")
test5 = test "Fail: f(x) == g(y)" (Func "f" [Var "x"]) (Func "g" [Var "y"])
test6 = test "Ok: f(x) == f(y)" (Func "f" [Var "x"]) (Func "f" [Var "y"])

runTests = do {test1; test2; test3; test4; test5; test6}
