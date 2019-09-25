module Model where

import Digits
import DigitAssignment

import Data.Maybe (fromJust)
import Data.List (groupBy, sort)
import Data.Function (on)

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
