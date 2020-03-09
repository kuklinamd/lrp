module DPLL where

import Data.List
import Data.Maybe (fromJust)

data Var = Lit String
         | Neg String
         deriving (Show, Eq, Ord)

getName (Lit x) = x
getName (Neg x) = x

sameName x y = (getName x) == (getName y)

sameType (Lit _) (Lit _) = True
sameType (Neg _) (Neg _) = True
sameType _       _       = False

isLit (Lit _) = True
isLit _       = False

isNeg (Neg _) = True
isNeg _       = False

type Clause = [Var]
type Cnf = [Clause]

genSubst :: [Var] -> [(String, Bool)]
genSubst = fmap (\c -> (getName c, if isLit c then True else False))

dpll :: Cnf -> Maybe [Var]
dpll = dpll' []

dpll' :: [Var] -> Cnf -> Maybe [Var]
dpll' vars [] = Just vars
dpll' vars cnf = do
  (vars', cnf') <- unitPropagate [] cnf
  let (vars'', cnf'') = pureLiteralsAssign vars' cnf'
  case chooseLiteral cnf'' of
    Nothing -> Just vars''
    Just (lit, cnf''') -> dpll' vars'' ([lit] : cnf''')

chooseLiteral :: Cnf -> Maybe (Var, Cnf)
chooseLiteral [] = Nothing
chooseLiteral (c:cnf) = Just (head c, cnf)

unitPropagate :: [Var] -> Cnf -> Maybe ([Var], Cnf)
unitPropagate acc c
  | not $ hasLone c
  = Just (acc, c)
 | otherwise
  =
   let lit = head $ fromJust $ find lone c
       res = litPropagate lit c
   in maybe Nothing (unitPropagate (lit:acc)) res
   where
     litPropagate :: Var -> Cnf -> Maybe Cnf
     litPropagate v = fmap (filter (not . null)) . sequence . fmap (up' v)
     
     up' :: Var -> Clause -> Maybe Clause
     up' v c =
       let (vs, rest) = partition (sameName v) c
       in
       if all1 (not . sameType v) vs && null rest then Nothing
       else if all1 isLit vs then Just [] else Just rest

pureLiteralsAssign :: [Var] -> Cnf -> ([Var], Cnf)
pureLiteralsAssign vars cnf
  | Just lit <- findPureLiteral cnf
  = let (lit', cnf') = pureLiteralAssign lit cnf
    in pureLiteralsAssign (lit':vars) cnf'
  | otherwise
  = (vars, cnf)

pureLiteralAssign :: Var -> Cnf -> (Var, Cnf)
pureLiteralAssign lit cs = (lit, filter (lit /=) <$> cs)

findPureLiteral :: Cnf -> Maybe Var
findPureLiteral = fmap head . find lone . groupBy sameName . sortVar . uniq

lone = (1 ==) . length

hasLone = not . null . filter lone

uniq :: Cnf -> [Var]
uniq = map head . group . sort . concat

simplify :: Clause -> Clause
simplify =  concat . filter (not . both isLit isNeg) . groupBy sameName

sortVar = sortBy (\v1 v2 -> compare (getName v1) (getName v2))

both f g xs = any1 f xs && any1 g xs

any1 f [] = False
any1 f (x:xs) = f x || any1 f xs

all1 f [] = False
all1 f [x] = f x
all1 f (x:xs) = f x && all1 f xs

cs1 = [[Lit "p", Neg "q"], [Neg "p", Neg "r"], [Lit "q"]]
cs2 = [[Lit "a", Lit "b"], [Neg "a", Lit "c"], [Neg "c", Lit "d"], [Lit "a"]]
cs3 = [[Lit "x"], [Neg "x"]]
cs4 = [[Lit "x", Neg "y"], [Neg "x", Lit "y"]]
cs5 = [[Lit "x", Lit "y"]]
