{-# LANGUAGE TupleSections, DeriveFunctor #-}

module Prolog (module Prolog) where
    
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.List (intercalate, find, findIndex, partition)
import Data.Maybe (fromMaybe, isJust, fromJust, isNothing)

import Control.Arrow (first, second)
import Control.Monad (foldM)

import Debug.Trace

data Name = Name { nmStr :: String, nmIdx :: Int } deriving (Eq, Ord)

var = Var . flip Name 0

data Preterm a = Var a | Val String | Ctr String [Term] deriving (Eq, Functor)

type Term = Preterm Name

data Prefun a = Fn { fnName :: String, fnArgs :: [Preterm a] }
  deriving (Functor)
type Fun = Prefun Name

data Preclause a = Cls { clsHead :: Prefun a, clsBody :: Maybe [Prefun a] }
  deriving (Functor)
type Clause = Preclause Name

newtype Predef a = Def [Preclause a]
  deriving (Functor)
type Def = Predef Name

newtype Program = Program { defs :: [(String, Def)] }

newtype Goal = Goal [Fun]

findDef :: Program -> String -> Def
findDef (Program defs) name
  | Just def <- lookup name defs
  = def
  | otherwise
  = error $ "No <" ++ name ++ "> def in the program"

--
-- Rename
--
rename :: Int -> Name -> Name
rename i name = name { nmIdx = i }

renameTerm :: Int -> Term -> Term
renameTerm i = fmap (rename i)

renameFun :: Int -> Fun -> Fun
renameFun i = fmap (rename i)

renameClause :: Int -> Clause -> Clause
renameClause i = fmap (rename i)

--
-- Unification
--

type Subst = [(Name, Term)]

insert :: Subst -> Name -> Term -> Maybe Subst
insert s n t
  | t' == Just t = Just s
  | Nothing <- t' = Just $ (n, t) : s
  | otherwise = Nothing
  where t' = lookup n s

unionSubst :: Subst -> Subst -> Maybe Subst
unionSubst = foldM (uncurry . insert)

occursCheck :: Name -> Term -> Bool
occursCheck name term = not $ occurs name term

occurs name term = name `elem` freeVars term

freeVars :: Term -> Set.Set Name
freeVars (Val _) = Set.empty
freeVars (Var x) = Set.singleton x
freeVars (Ctr _ args) = Set.unions (freeVars <$> args)

unify :: Subst -> Term -> Term -> Maybe Subst
unify s t1 t2
  | t1' <- fromMaybe t1 (walk s t1)
  , t2' <- fromMaybe t2 (walk s t2)
  = unify' s t1' t2'

walk :: Subst -> Term -> Maybe Term
walk s (Var n) = lookup n s
walk s t       = Just t

unify' :: Subst -> Term -> Term -> Maybe Subst
unify' s (Val a) (Val b)
  | a == b
  = Just s
unify' s (Var a) (Var b)
  | a == b
  = Just s
unify' s (Var a) t
  | occursCheck a t
  = insert s a t
unify' s t (Var a)
  | occursCheck a t
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
    let xs' = applySubst s' xs
    let ys' = applySubst s' ys
    s'' <- unifyList s xs' ys'
    unionSubst s' s''

applySubst :: Subst -> [Term] -> [Term]
applySubst s ts = [applyTerm s t | t <- ts]

applyTerm _  t@(Val _) = t
applyTerm [] t@(Var _) = t
applyTerm ((name, term):ss) t@(Var v)
  | name == v
  = applyTerm ss term
  | otherwise
  = applyTerm ss t
applyTerm s (Ctr n ts)
  = Ctr n (applySubst s ts)

applySubstToBody :: Subst -> [Fun] -> [Fun]
applySubstToBody s fs = applySubstToFun s <$> fs
  where
    applySubstToFun s (Fn name ts) = Fn name $ applySubst s ts


getClause :: Int -> Def -> Clause
getClause i (Def cls) = cls !! i

getGoal :: Int -> Goal -> Fun
getGoal i (Goal gl) = gl !! i

reduceSubst :: Set.Set Name -> Subst -> Subst
reduceSubst ns ss =
  let (rs, ss') = partition (\(n,t) -> Set.member n ns) ss
      (nms, ts)  = unzip rs
  in reduceSubst' nms ts ss' (length ss')

reduceSubst' ns ts _ 0 = zip ns ts
reduceSubst' ns ts ss n = reduceSubst' ns (applySubst ss ts) ss (pred n)

nextName :: Int -> Int
nextName = succ

defSize :: Program -> Fun -> Int
defSize prg (Fn name _)
  | Def cls <- findDef prg name
  = length cls

freeVarsInGoal :: Goal -> Set.Set Name
freeVarsInGoal (Goal fs) = Set.unions (freeVarsInFn <$> fs)

freeVarsInFn :: Fun -> Set.Set Name
freeVarsInFn (Fn _ ts) = Set.unions (freeVars <$> ts)

res prg query = reduceSubst (freeVarsInGoal query) <$> res' prg query

res' prg query@(Goal q) = resolve' 1 prg 0 [] q

renameDef :: Int -> Def -> Def
renameDef nameSupply (Def def) =
  Def $ foldr (\cl ds -> renameClause nameSupply cl : ds) [] def

resolve' _ _ _ subst [] = [subst]
resolve' nameSupply prg idx subst q@(g@(Fn name _):gs) =
 -- trace ("\nResolve " ++ show q ++ " in " ++ show subst) $
 let
    ~(Def def) = renameDef nameSupply $ findDef prg name
    -- Next level of evaluation tree
    children = unifyWithClause subst g <$> def
    -- Left only unificated children
 -- in trace ("\nUnified: " ++ show children) $ let
    branches = fromJust <$> filter isJust children

    ns' = nextName nameSupply
 in branches >>= (\(s, g) -> resolve' ns' prg idx s (g ++ gs))

unifyWithClause :: Subst -> Fun -> Clause -> Maybe (Subst, [Fun])
unifyWithClause subst g@(Fn name args) (Cls head@(Fn name' args') body)
  | Just subst' <- unifyList subst args args'
  = Just (subst', applySubstToBody subst' $ fromMaybe [] body)
  | otherwise
  = Nothing

isUnifiableArgs :: [Term] -> [Term] -> Bool
isUnifiableArgs t1 t2
 | length t1 == length t2
 = and $ uncurry isUnifiable <$> zip t1 t2
 | otherwise
 = False

isUnifiable :: Term -> Term -> Bool
isUnifiable t1 = isJust . unify [] t1

--
-- Printing
--
instance Show Name where
  show (Name s 0) = s
  show (Name s i) = s ++ "_" ++ show i

instance Show a => Show (Preterm a) where
  show (Var s) = show s
  show (Val s) = "`" ++ s
  show (Ctr name args) = name ++ "(" ++ intercalate ", " (show <$> args) ++ ")"

instance Show a => Show (Prefun a) where
  show (Fn name args) = name ++ "(" ++ intercalate ", " (show <$> args) ++ ")"

instance Show a => Show (Preclause a) where
  show (Cls head Nothing) = show head ++ "."
  show (Cls head (Just body)) = show head ++ " :- " ++ intercalate ", " (show <$> body) ++ "."

instance Show a => Show (Predef a) where
  show (Def cs) = intercalate "\n" (show <$> cs)

instance Show Program where
  show = intercalate "\n" . fmap (show . snd) . defs

instance Show Goal where
  show (Goal gl) = intercalate "," $ show <$> gl

--
-- Examples
--
example1 = Program [("mother_child" , mc), ("father_child", fc), ("parent_child", pc), ("siblings", sb)]
  where
    mc = Def [Cls (Fn "mother_child" [Val "Mama", Val "Child1"]) Nothing]
    fc = Def [Cls (Fn "father_child" [Val "Papa", Val "Child1"]) Nothing
             ,Cls (Fn "father_child" [Val "Papa", Val "Child2"]) Nothing
             ,Cls (Fn "father_child" [Val "Gran", Val "Papa"]) Nothing]
    pc = Def [Cls (Fn "parent_child" [var "X", var "Y"]) (Just [Fn "mother_child" [var "X", var "Y"]])
             ,Cls (Fn "parent_child" [var "X", var "Y"]) (Just [Fn "father_child" [var "X", var "Y"]])]
    sb = Def [Cls (Fn "siblings" [var "X", var "Y"]) (Just [Fn "parent_child" [var "Z", var "X"], Fn "parent_child" [var "Z", var "Y"]])]

query11 = Goal [Fn "siblings" [Val "Child1", Val "Child2"]]
query12 = Goal [Fn "siblings" [Val "Child1", Val "Child3"]]
query13 = Goal [Fn "siblings" [Val "Child1", var "X"]]
query14 = Goal [Fn "siblings" [var "Y", var "X"]]

cons x xs = Ctr "cons" [x, xs]
nil = Ctr "nil" []

suc x = Ctr "suc" [x]
zero  = Ctr "zero" []

one = suc zero
two = suc $ suc zero

example2 = Program [("append", app)]
  where
    app = Def [Cls (Fn "append" [nil, var "X", var "X"]) Nothing
              ,Cls (Fn "append" [cons (var "H") (var "T"), var "Y", cons (var "H") (var "TY")])
                   (Just [Fn "append" [var "T", var "Y", var "TY"]])
              ]
-- app([1], X, [1, 2])
query21 = Goal [Fn "append" [cons one nil, var "X", cons one $ cons two nil]]
-- app(Y, X, [1, 2])
query22 = Goal [Fn "append" [var "Y", var "X", cons one $ cons two nil]]
-- app([H|T], Y, R)
query23 = Goal [Fn "append" [cons (var "H") (var "T"), var "Y", var "R"]]

example3 = Program [("p", p), ("q", q), ("r", r), ("s", s), ("u", u)]
  where
    p = Def [Cls (Fn "p" [Val "a"    ]) Nothing
            ,Cls (Fn "p" [var "X"]) $ Just [Fn "q" [var "X"], Fn "r" [var "X"]]
            ,Cls (Fn "p" [var "X"]) $ Just [Fn "u" [var "X"]]]
    q = Def [Cls (Fn "q" [var "X"]) $ Just [Fn "s" [var "X"]]]
    r = Def [Cls (Fn "r" [Val "a"]) Nothing
            ,Cls (Fn "r" [Val "b"]) Nothing]
    s = Def [Cls (Fn "s" [Val "a"]) Nothing
            ,Cls (Fn "s" [Val "b"]) Nothing
            ,Cls (Fn "s" [Val "c"]) Nothing]
    u = Def [Cls (Fn "u" [Val "d"]) Nothing]

-- X = a, a, b, d
query31 = Goal [Fn "p" [var "X"]]


example4 = Program [("list", lst)]
  where
    lst = Def [Cls (Fn "list" [nil]) Nothing
              ,Cls (Fn "list" [cons (var "H") (var "T")]) $ Just [Fn "list" [var "T"]]]

query4 = Goal [Fn "list" [var "L"]]

example5 = Program [("plist", plst), ("p", p)]
  where
    plst = Def [Cls (Fn "plist" [nil]) Nothing
                ,Cls (Fn "plist" [cons (var "H") (var "T")]) $ Just [Fn "p" [var "H"], Fn "plist" [var "T"]]]

    p = Def [Cls (Fn "p" [zero]) Nothing
            ,Cls (Fn "p" [one])  Nothing]

query5 = Goal [Fn "plist" [var "X"]]

--
-- Test subst
--

testUnify predicate t1 t2 = do
  let s = unify [] t1 t2
  if predicate s
  then return ()
  else putStrLn $ "Wrong answer: unifier <" ++ show s ++ "> for t1 = " ++ show t1 ++ " t2 = " ++ show t2

test1 = testUnify isJust (var "x") (var "y")
test2 = testUnify isJust (var "x") (var "x")
test3 = testUnify isJust (var "x") (Ctr "f" [])
test4 = testUnify isNothing (Ctr "g" [var "x"]) (var "x")
test5 = testUnify isNothing (Ctr "f" [var "x"]) (Ctr "g" [var "y"])
test6 = testUnify isJust (Ctr "f" [var "x"]) (Ctr "f" [var "y"])
test7 = testUnify isNothing (Ctr "f" [var "X", var "X", var "X"]) (Ctr "f" [Val "a", Val "a", Val "b"])
test8 = testUnify isJust (Ctr "f" [Ctr "g" [Val "p", var "L"], var "Y", var "Y"]) (Ctr "f" [var "X", var "X", Ctr "g" [var "Z", Val "t"]])

runUnifyTests = do {test1; test2; test3; test4; test5; test6; test7; test8}
