{-# LANGUAGE ScopedTypeVariables #-}
module Eval where

import Formula
import Control.Arrow ((&&&))

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
