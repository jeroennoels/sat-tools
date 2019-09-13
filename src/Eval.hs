{-# LANGUAGE ScopedTypeVariables #-}
module Eval where

import Formula
import Clauses

import Control.Arrow ((&&&))
import Data.Set (Set)
import qualified Data.Set as Set

data Assignment i = Assignment {domain :: [i], assign :: i -> Bool}

instance Show i => Show (Assignment i) where
  show (Assignment dom f) = show $ map (id &&& f) dom

evaluate :: forall i . Formula i -> Assignment i -> Bool
evaluate x a = eval x where
  eval :: Formula i -> Bool
  eval (Var i) = assign a i
  eval (Not x) = not (eval x)
  eval (Or x y) = eval x || eval y
  eval (And x y) = eval x && eval y
  eval (Equiv x y) = eval x == eval y
  eval (Implies x y) = if eval x then eval y else True

characteristic :: Ord i => Set i -> Set i -> Assignment i
characteristic dom subset =
  Assignment { domain = Set.toList dom,
               assign = flip Set.member subset }

allAssignments :: forall i . Ord i => Set i -> [Assignment i]
allAssignments vars = map (characteristic vars) subsets
  where
    subsets :: [Set i]
    subsets = Set.toList (Set.powerSet vars)

equalOn :: Formula i -> Formula i -> Assignment i -> Bool
equalOn x y a = evaluate x a == evaluate y a

evalLiteral :: Assignment i -> Literal i -> Bool
evalLiteral a (Positive x) = assign a x
evalLiteral a (Negative x) = not (assign a x)

evalClauses :: [Clause i] -> Assignment i -> Bool
evalClauses cs a = all eval cs
  where eval (Clause xs) = any (evalLiteral a) xs

equivalentOn :: [Clause i] -> Formula i -> Assignment i -> Bool
equivalentOn cs f a = evalClauses cs a == evaluate f a
