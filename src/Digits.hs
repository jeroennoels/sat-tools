{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Digits where

import Formula
import Eval

import Data.Maybe (fromJust)
import Data.List (groupBy, sort)
import Data.Function (on)

class SignSymmetric j where
  flipPosNeg :: j -> j

-- Ternary digits in {-1,0,1}.
-- Think of i as coarse grained and j as fine grained.
class IdentifyT1 i j | j -> i where
  posT1 :: i -> Formula j
  negT1 :: i -> Formula j
  zeroT1 :: i -> Formula j
  isValidT1 :: i -> Formula j
  -- default implementations
  zeroT1 i = Not (posT1 i) `And` Not (negT1 i)
  isValidT1 i = Not (posT1 i `And` negT1 i)


-- Ternary digit in {-2,-1,0,1,2}.
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

equivalentT12 :: (IdentifyT1 i1 j, IdentifyT2 i2 j) => i1 -> i2 -> Formula j
equivalentT12 a b = conjunction [
  posT1 a  `Equiv` plusOneT2 b,
  negT1 a  `Equiv` minusOneT2 b,
  zeroT1 a `Equiv` zeroT2 b]


data Fine1 = Pos1 | Neg1 deriving (Eq, Ord, Read, Show)
data Fine2 = Pos2 | Neg2 | Even2 deriving (Eq, Ord, Read, Show)

data T12 i1 i2 = T1 i1 Fine1
               | T2 i2 Fine2
               deriving (Eq, Ord, Read, Show)

flipPosNegT12 :: T12 i1 i2 -> T12 i1 i2
flipPosNegT12 (T1 i Pos1) = T1 i Neg1
flipPosNegT12 (T1 i Neg1) = T1 i Pos1
flipPosNegT12 (T2 i Pos2) = T2 i Neg2
flipPosNegT12 (T2 i Neg2) = T2 i Pos2
flipPosNegT12 x@(T2 _ Even2) = x


instance SignSymmetric (T12 i1 i2) where
  flipPosNeg = flipPosNegT12

instance IdentifyT1 i1 (T12 i1 i2) where
  posT1 i = Var (T1 i Pos1)
  negT1 i = Var (T1 i Neg1)

instance IdentifyT2 i2 (T12 i1 i2) where
  posT2 i = Var (T2 i Pos2)
  negT2 i = Var (T2 i Neg2)
  evenT2 i = Var (T2 i Even2)

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

-- Semantics.
getDigitT2 :: Eq i2 => Assignment (T12 i1 i2) -> i2 -> DigitT2
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

phi2Base3 :: [DigitT2] -> Maybe Int
phi2Base3 digits = lsdfBase3 `fmap` sequence (map phi2 digits)

lsdfBase3 :: [Int] -> Int
lsdfBase3 (d:ds) = d + 3 * lsdfBase3 ds
lsdfBase3 [] = 0

sameDigit :: (Eq i1, Eq i2) => T12 i1 i2 -> T12 i1 i2 -> Bool
sameDigit (T1 a _ ) (T1 b _ ) = a == b
sameDigit (T2 a _ ) (T2 b _ ) = a == b
sameDigit _ _ = False

groupDigits :: (Eq i1, Eq i2, Ord i1, Ord i2) =>
    [(T12 i1 i2, Bool)] -> [[(T12 i1 i2, Bool)]]
groupDigits = map sort . groupBy (sameDigit `on` fst)

-- This is a bit of a hack: we assume the input is ordered, complete
-- and about one digit only.
toDigit :: (Eq i1, Eq i2) => [(T12 i1 i2, Bool)] ->
    Either (i1, DigitT1) (i2, DigitT2)
toDigit [(T1 a Pos1, p), (T1 b Neg1, n)] | a == b =
    Left (a, DigitT1 {isPos1 = p, isNeg1 = n})
toDigit [(T2 a Pos2, p), (T2 b Neg2, n), (T2 c Even2, e)] | a == b && b == c =
    Right (a, DigitT2 {isPos2 = p, isNeg2 = n, isEven2 = e})
toDigit _ = error "input assumptions not satisfied"


showDigit :: (Show i1, Show i2) => Either (i1, DigitT1) (i2, DigitT2) -> String
showDigit (Left  (i, x)) = show i ++ "(" ++ show (fromJust $ phi1 x) ++ ")"
showDigit (Right (i, x)) = show i ++ "(" ++ show (fromJust $ phi2 x) ++ ")"

interpretation :: (Eq i1, Eq i2, Ord i1, Ord i2, Show i1, Show i2) =>
    [(T12 i1 i2, Bool)] -> [String]
interpretation = map (showDigit . toDigit) . groupDigits

abstraction :: (Eq a1, Eq a2, IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    [(a1,i1)] -> [(a2,i2)] -> T12 a1 a2 -> Formula j
abstraction assoc1 _ (T1 a Pos1) = posT1 (fromJust $ lookup a assoc1)
abstraction assoc1 _ (T1 a Neg1) = negT1 (fromJust $ lookup a assoc1)
abstraction _ assoc2 (T2 a Pos2) = posT2 (fromJust $ lookup a assoc2)
abstraction _ assoc2 (T2 a Neg2) = negT2 (fromJust $ lookup a assoc2)
abstraction _ assoc2 (T2 a Even2) = evenT2 (fromJust $ lookup a assoc2)

