module Formula where

import Data.Set (Set)
import qualified Data.Set as Set

-- The type parameter represents the type of identifier we want to use
-- to label the variables. For an example, think String or Int.

data Formula i =
  Var i
  | Not (Formula i)
  | Or (Formula i) (Formula i)
  | And (Formula i) (Formula i)
  | Equiv (Formula i) (Formula i)
  | Implies (Formula i) (Formula i)

-- In many examples we simply use Int to label the variables.
newtype IntLabel = IntLabel Int deriving (Eq, Ord)

instance Show IntLabel where
  show (IntLabel n) = show n

-- The following implementation of Show is very inefficient and only
-- intended to debug small examples.

showBinop :: Show i => Formula i -> String -> Formula i -> String
showBinop x op y = '(' : show x ++ spaced ++ show y ++ ")"
  where spaced = ' ' : op ++ [' ']

instance Show i => Show (Formula i) where
  show (Var i) = show i
  show (Not x) = '~' : show x
  show (Or x y) = showBinop x "or" y
  show (And x y) = showBinop x "and" y
  show (Equiv x y) = showBinop x "<=>" y
  show (Implies x y) = showBinop x "=>" y

-- Find all distinct Variables occurring in a given formula.
variables :: Ord i => Formula i -> Set i
variables (Var i) = Set.singleton i
variables (Not x) = variables x
variables (Or x y) = variables x `Set.union` variables y
variables (And x y) = variables x `Set.union` variables y
variables (Equiv x y) = variables x `Set.union` variables y
variables (Implies x y) = variables x `Set.union` variables y

-- Conjunctive normal form.  Inspired by:
-- https://github.com/chris-taylor/aima-haskell/tree/master/src/AI/Logic

-- The first step towards CNF is to eliminate all implications and
-- bicondionals.

impliesCNF ::  Formula i -> Formula i -> Formula i
impliesCNF x y = Not x `Or` y

equivCNF :: Formula i -> Formula i -> Formula i
equivCNF x y = impliesCNF x y `And` impliesCNF y x

elimImplication :: Formula i -> Formula i
elimImplication x@(Var _) = x
elimImplication (Not x) = Not (elimImplication x)
elimImplication (Or x y) = elimImplication x `Or` elimImplication y
elimImplication (And x y) = elimImplication x `And` elimImplication y
elimImplication (Equiv x y) = elimImplication x `equivCNF` elimImplication y
elimImplication (Implies x y) = elimImplication x `impliesCNF` elimImplication y

-- Using De Morgan's laws, we push negation down to the variables and
-- eliminate double negation along the way.  We assume implications
-- and bicondionals were eliminated beforehand.

moveNotDown :: Formula i -> Formula i
moveNotDown x@(Var _) = x
moveNotDown x@(Not (Var _)) = x
moveNotDown (Not (Not x)) = moveNotDown x
moveNotDown (Not (Or x y)) = moveNotDown (Not x) `And` moveNotDown (Not y)
moveNotDown (Not (And x y)) = moveNotDown (Not x) `Or` moveNotDown (Not y)
moveNotDown (And x y) = moveNotDown x `And` moveNotDown y
moveNotDown (Or x y) = moveNotDown x `Or` moveNotDown y
