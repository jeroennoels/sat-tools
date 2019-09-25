{-# LANGUAGE ScopedTypeVariables #-}
module DigitAssignment where

import Eval
import Digits

-- A concrete variable assignment that represents one T1 digit.
data DigitT1 = DigitT1 {isPos1 :: Bool, isNeg1 :: Bool}

getDigitT1 :: Eq i1 => Assignment (T12 i1 i2) -> i1 -> DigitT1
getDigitT1 a i = DigitT1 {
  isPos1 = assign a (T1 i Pos1),
  isNeg1 = assign a (T1 i Neg1)}

-- Semantics.
phi1 :: DigitT1 -> Maybe Int
phi1 (DigitT1 True False) = Just 1
phi1 (DigitT1 False True) = Just (-1)
phi1 (DigitT1 False False) = Just 0
phi1 (DigitT1 True True) = Nothing  -- forbidden

-- A concrete variable assignment that represents one T2 digit.
data DigitT2 = DigitT2 {isPos2 :: Bool, isNeg2 :: Bool, isEven2 :: Bool}

getDigitT2 :: Eq i2 => Assignment (T12 i1 i2) -> i2 -> DigitT2
getDigitT2 a i = DigitT2 {
  isPos2 = assign a (T2 i Pos2),
  isNeg2 = assign a (T2 i Neg2),
  isEven2 = assign a (T2 i Even2)}

-- Semantics.
phi2 :: DigitT2 -> Maybe Int
phi2 (DigitT2 True False True) = Just 2
phi2 (DigitT2 True False False) = Just 1
phi2 (DigitT2 False False True) = Just 0
phi2 (DigitT2 False True False) = Just (-1)
phi2 (DigitT2 False True True) = Just (-2)
phi2 _ = Nothing  -- forbidden

phi2Base3 :: [DigitT2] -> Maybe Int
phi2Base3 digits = lsdfBase3 `fmap` sequence (map phi2 digits)

lsdfBase3 :: [Int] -> Int
lsdfBase3 (d:ds) = d + 3 * lsdfBase3 ds
lsdfBase3 [] = 0
