{-# LANGUAGE ScopedTypeVariables #-}
module AddT1 (addDigitsT1) where

import Formula
import Clauses
import Digits


-- Exploit two symmetries: commutativity and flipping signs
addDigitsT1 :: (IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
    i1 -> i1 -> i2 -> Formula j
addDigitsT1 a b x = commute `And` fmap flipPosNeg commute
  where commute  = quadrant a b x `And` quadrant b a x


quadrant :: (IdentifyT1 i1 j, IdentifyT2 i2 j) => i1 -> i1 -> i2 -> Formula j
quadrant a b x = conjunction [
  (posT1 a `And` posT1 b)   `Implies` plusTwoT2 x,  -- 1+1 = 2
  (posT1 a `And` zeroT1 b)  `Implies` plusOneT2 x,  -- 1+0 = 1
  (posT1 a `And` negT1 b)   `Implies` zeroT2 x,     -- 1-1 = 0
  (zeroT1 a `And` zeroT1 b) `Implies` zeroT2 x]     -- 0+0 = 0
