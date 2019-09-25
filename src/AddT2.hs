{-# LANGUAGE ScopedTypeVariables #-}
module AddT2 (addDigitsT2) where

import Formula
import Clauses
import Digits


-- Exploit two symmetries: commutativity and flipping signs
makeFormula :: (IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
    i2 -> i2 -> i1 -> i1 -> Formula j
makeFormula a b x y = commute `And` fmap flipPosNeg commute
  where
    commute = quadrant a b x y `And`
              quadrant b a x y

quadrant :: (IdentifyT1 i1 j, IdentifyT2 i2 j) =>
   i2 -> i2 -> i1 -> i1 -> Formula j
quadrant a b x y = conjunction [
  (plusTwoT2 a `And` plusTwoT2 b)         -- 2 + 2
  `Implies` (posT1 x `And` posT1 y),      -- becomes (1,1)
  (plusTwoT2 a `And` plusOneT2 b)         -- 2 + 1
  `Implies` (posT1 x `And` zeroT1 y),     -- becomes (1,0)
  ((plusTwoT2 a `And` zeroT2 b) `Or`      -- 2 + 0
   (plusOneT2 a `And` plusOneT2 b))       -- 1 + 1
  `Implies` (posT1 x `And` negT1 y),      -- becomes (1,-1)
  ((plusTwoT2 a `And` minusOneT2 b) `Or`  -- 2 + (-1)
   (plusOneT2 a `And` zeroT2 b))          -- 1 + 0
  `Implies` (zeroT1 x `And` posT1 y),     -- becomes (0,1)
  ((plusTwoT2 a `And` minusTwoT2 b) `Or`  -- 2 + (-2)
   (plusOneT2 a `And` minusOneT2 b) `Or`  -- 1 + (-1)
   (zeroT2 a `And` zeroT2 b))             -- 0 + 0
  `Implies` (zeroT1 x `And` zeroT1 y)]    -- becomes (0,0)


-- Think of this as "compiling" into a reusable template
template :: [Clause CharId]
template = formulaToClauses $ makeFormula 'a' 'b' 'x' 'y'

addDigitsT2 :: forall i1 i2 j . (IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    i2 -> i2 -> i1 -> i1 -> [Clause j]
addDigitsT2 a b x y = map (fmap substitution) template
  where
    substitution :: CharId -> j
    substitution = identifier . abstraction [('x',x),('y',y)] [('a',a),('b',b)]
