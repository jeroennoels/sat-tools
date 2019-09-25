module Model where

import Digits
import DigitAssignment

import Data.Maybe (fromJust)
import Data.List (groupBy, sort)
import Data.Function (on)
import Data.Either (partitionEithers)


sameDigit :: (Eq i1, Eq i2) => T12 i1 i2 -> T12 i1 i2 -> Bool
sameDigit (T1 a _ ) (T1 b _ ) = a == b
sameDigit (T2 a _ ) (T2 b _ ) = a == b
sameDigit _ _ = False

groupDigits :: (Eq i1, Eq i2, Ord i1, Ord i2) =>
    [(T12 i1 i2, Bool)] -> [[(T12 i1 i2, Bool)]]
groupDigits = map sort . groupBy (sameDigit `on` fst)


data Model1 i = Model1 i DigitT1
data Model2 i = Model2 i DigitT2

instance Show i => Show (Model1 i) where
  show (Model1 i x) = show i ++ "(" ++ show (fromJust $ phi1 x) ++ ")"

instance Show i => Show (Model2 i) where
  show (Model2 i x) = show i ++ "(" ++ show (fromJust $ phi2 x) ++ ")"


-- This is a bit of a hack: we assume the input is ordered, complete
-- and about one digit only.

toDigitModel :: (Eq i1, Eq i2) => [(T12 i1 i2, Bool)] ->
  Either (Model1 i1) (Model2 i2)
-- left
toDigitModel [(T1 a Pos1, p), (T1 b Neg1, n)]
  | a == b =
  Left $ Model1 a (DigitT1 {isPos1 = p, isNeg1 = n})
-- right
toDigitModel [(T2 a Pos2, p), (T2 b Neg2, n), (T2 c Even2, e)]
  | a == b && b == c =
  Right $ Model2 a (DigitT2 {isPos2 = p, isNeg2 = n, isEven2 = e})
-- bad input
toDigitModel _ = error "input assumptions not satisfied"


interpretation :: (Eq i1, Eq i2, Ord i1, Ord i2, Show i1, Show i2) =>
    [(T12 i1 i2, Bool)] -> ([Model1 i1], [Model2 i2])
interpretation = partitionEithers . map toDigitModel . groupDigits
