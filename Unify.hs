module Unify where

import Data.Maybe (fromMaybe)

type Name = String

data Term =
    Var { var :: Name }
  | Func { name :: Name, args :: [Term] }
  deriving Show

type Subst = [(Name, Term)]

unify :: Subst -> Term -> Term -> Maybe Subst
unify s t1 t2
  | t1' <- fromMaybe t1 (walk s t1)
  , t2' <- fromMaybe t2 (walk s t2)
  = unify' s t1' t2'
  where
    unify' :: Subst -> Term -> Term -> Maybe Subst
    unify' s (Var n1) t2@(Var n2)
      | n1 == n2
      = Just s
      | otherwise
      = Just $ unite [(n1, t2)] s
    unify' s (Func n1 a1) (Func n2 a2)
      | n1 == n2
      , length a1 == length a2
      = foldl1 unite <$> (sequence $ uncurry (unify s) <$> zip a1 a2)
    unify' s t1@(Var n1) t2
      | not $ n1 `elem` freeVars t2
      = Just $ unite [(n1, t2)] s
    unify' s t1 t2@(Var n2)
      | not $ n2 `elem` freeVars t1
      = Just $ unite [(n2, t2)] s
    unify' _ _ _
      = Nothing

    unite :: Subst -> Subst -> Subst
    unite = (++)

    freeVars :: Term -> [Name]
    freeVars (Var n) = [n]
    freeVars (Func _ args) = concat (freeVars <$> args)

    walk :: Subst -> Term -> Maybe Term
    walk s (Var n) = lookup n s
    walk s t = Just t


test msg t1 t2 = do
  putStrLn $ ">>>" ++ msg
  let s = unify [] t1 t2
  putStrLn $ "Result: " ++ show s

test1 = test "Ok: x == y" (Var "x") (Var "y")
test2 = test "Ok: x == x" (Var "x") (Var "x")
test3 = test "Ok: x == f()" (Var "x") (Func "f" [])
test4 = test "Fail: g(x) == x" (Func "g" [Var "x"]) (Var "x")
test5 = test "Fail: f(x) = g(y)" (Func "f" [Var "x"]) (Func "g" [Var "y"])
test6 = test "Ok: f(x) = f(y)" (Func "f" [Var "x"]) (Func "f" [Var "y"])

runTests = do {test1; test2; test3; test4; test5; test6}
