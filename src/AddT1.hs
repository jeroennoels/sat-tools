{-# LANGUAGE ScopedTypeVariables #-}
module AddT1 (addDigitsT1) where

import Formula
import Clauses
import Digits


-- Exploit two symmetries: commutativity and flipping signs
makeFormula :: (IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
    i1 -> i1 -> i2 -> Formula j
makeFormula a b x = commute `And` fmap flipPosNeg commute
  where commute  = quadrant a b x `And` quadrant b a x


quadrant :: (IdentifyT1 i1 j, IdentifyT2 i2 j) => i1 -> i1 -> i2 -> Formula j
quadrant a b x = conjunction [
  (posT1 a `And` posT1 b)   `Implies` plusTwoT2 x,  -- 1+1 = 2
  (posT1 a `And` zeroT1 b)  `Implies` plusOneT2 x,  -- 1+0 = 1
  (posT1 a `And` negT1 b)   `Implies` zeroT2 x,     -- 1-1 = 0
  (zeroT1 a `And` zeroT1 b) `Implies` zeroT2 x]     -- 0+0 = 0


-- Think of this as "compiling" into a reusable template
template :: [Clause CharId]
template = formulaToClauses $ makeFormula 'a' 'b' 'x'

addDigitsT1 :: forall i1 i2 j . (IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    i1 -> i1 -> i2 -> [Clause j]
addDigitsT1 a b x = map (fmap substitution) template
  where
    substitution :: CharId -> j
    substitution = identifier . abstraction [('a',a),('b',b)] [('x',x)]
