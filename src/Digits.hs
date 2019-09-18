{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
module Digits where

import Formula
import Eval

class SignSymmetric j where
  flipPosNeg :: j -> j

-- Ternary digits in {-1,0,1}
class IdentifyT1 i j | j -> i where
  posT1 :: i -> Formula j
  negT1 :: i -> Formula j
  zeroT1 :: i -> Formula j
  isValidT1 :: i -> Formula j
  -- default implementations
  zeroT1 i = Not (posT1 i) `And` Not (negT1 i)
  isValidT1 i = Not (posT1 i `And` negT1 i)


-- Ternary digit in {-2,-1,0,1,2}
class IdentifyT2 i j | j -> i where
  posT2 :: i -> Formula j
  negT2 :: i -> Formula j
  evenT2 :: i -> Formula j
  oddT2 :: i -> Formula j
  zeroT2 :: i -> Formula j
  isValidT2 :: i -> Formula j
  plusTwoT2 :: i -> Formula j
  minusTwoT2 :: i -> Formula j
  plusOneT2 :: i -> Formula j
  minusOneT2 :: i -> Formula j
  -- default implementations
  oddT2 = Not . evenT2
  zeroT2 i = Not (posT2 i) `And` Not (negT2 i)
  isValidT2 i = Not (posT2 i `And` negT2 i) `And` (zeroT2 i `Implies` evenT2 i)
  minusTwoT2 i = evenT2 i `And` negT2 i
  plusTwoT2 i = evenT2 i `And` posT2 i
  plusOneT2 i = oddT2 i `And` posT2 i
  minusOneT2 i = oddT2 i `And` negT2 i


data Fine1 = Pos1 | Neg1 deriving (Eq, Ord, Show)
data Fine2 = Pos2 | Neg2 | Even2 deriving (Eq, Ord, Show)

data T12 i = T1 i Fine1
           | T2 i Fine2
           deriving (Eq, Ord, Show)

flipPosNegT12 :: T12 i -> T12 i
flipPosNegT12 (T1 i Pos1) = T1 i Neg1
flipPosNegT12 (T1 i Neg1) = T1 i Pos1
flipPosNegT12 (T2 i Pos2) = T2 i Neg2
flipPosNegT12 (T2 i Neg2) = T2 i Pos2
flipPosNegT12 x@(T2 _ Even2) = x


instance SignSymmetric (T12 i) where
  flipPosNeg = flipPosNegT12

instance IdentifyT1 i (T12 i) where
  posT1 i = Var (T1 i Pos1)
  negT1 i = Var (T1 i Neg1)

instance IdentifyT2 i (T12 i) where
  posT2 i = Var (T2 i Pos2)
  negT2 i = Var (T2 i Neg2)
  evenT2 i = Var (T2 i Even2)


-- A concrete variable assignment that represents one T1 digit.
data DigitT1 = DigitT1 {isPos1 :: Bool, isNeg1 :: Bool}

getDigitT1 :: Eq i => Assignment (T12 i) -> i -> DigitT1
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

-- Semantics.
getDigitT2 :: Eq i => Assignment (T12 i) -> i -> DigitT2
getDigitT2 a i = DigitT2 {
  isPos2 = assign a (T2 i Pos2),
  isNeg2 = assign a (T2 i Neg2),
  isEven2 = assign a (T2 i Even2)}

phi2 :: DigitT2 -> Maybe Int
phi2 (DigitT2 True False True) = Just 2
phi2 (DigitT2 True False False) = Just 1
phi2 (DigitT2 False False True) = Just 0
phi2 (DigitT2 False True False) = Just (-1)
phi2 (DigitT2 False True True) = Just (-2)
phi2 _ = Nothing  -- forbidden
