module Model where

import Digits
import DigitAssignment

import Data.Maybe (fromJust)
import Data.List (groupBy, sort, nub)
import Data.Function (on)
import Data.Either (partitionEithers)


sameDigit :: (Eq i1, Eq i2) => T12 i1 i2 -> T12 i1 i2 -> Bool
sameDigit (T1 a _ ) (T1 b _ ) = a == b
sameDigit (T2 a _ ) (T2 b _ ) = a == b
sameDigit _ _ = False

groupDigits :: (Eq i1, Eq i2, Ord i1, Ord i2) =>
    [(T12 i1 i2, Bool)] -> [[(T12 i1 i2, Bool)]]
groupDigits = map sort . groupBy (sameDigit `on` fst)


data DigitValue i = DigitValue i Int
  deriving Show

unsafeValueT1 :: Show i => i -> DigitT1 -> DigitValue i
unsafeValueT1 i x = case phi1 x of
  Just a -> DigitValue i a
  Nothing -> error $ "Not a valid digit: " ++ show i

unsafeValueT2 :: Show i => i -> DigitT2 -> DigitValue i
unsafeValueT2 i x = case phi2 x of
  Just a -> DigitValue i a
  Nothing -> error $ "Not a valid digit: " ++ show i


-- The next function is a bit of a hack: we assume the input is
-- ordered, complete and about one digit only.

digitValue :: (Eq i1, Eq i2, Show i1, Show i2) => [(T12 i1 i2, Bool)] ->
    Either (DigitValue i1) (DigitValue i2)
-- left
digitValue [(T1 a Pos1, p), (T1 b Neg1, n)]
  | a == b =
  Left . unsafeValueT1 a $ DigitT1 {isPos1 = p, isNeg1 = n}
-- right
digitValue [(T2 a Pos2, p), (T2 b Neg2, n), (T2 c Even2, e)]
  | a == b && b == c =
  Right . unsafeValueT2 a $ DigitT2 {isPos2 = p, isNeg2 = n, isEven2 = e}
-- bad input
digitValue _ = error "input assumptions not satisfied"


digitValues :: (Eq i1, Eq i2, Ord i1, Ord i2, Show i1, Show i2) =>
    [(T12 i1 i2, Bool)] -> ([DigitValue i1], [DigitValue i2])
digitValues = partitionEithers . map digitValue . groupDigits


idDigitValue :: DigitValue (Positional i) -> i
idDigitValue (DigitValue (Positional i _) _) = i

numberValue :: Eq i => [DigitValue (Positional i)] -> (i, Int)
numberValue ds = (id, sum (map term ds))
  where
    [id] = nub (map idDigitValue ds)
    term (DigitValue (Positional _ k) a) = a * 3^k

allNumberValues :: Eq i => [DigitValue (Positional i)] -> [(i, Int)]
allNumberValues = map numberValue . groupBy ((==) `on` idDigitValue)

interpretationT2 :: (Eq i1, Eq i2, Ord i1, Ord i2, Show i1, Show i2) =>
    [(T12 i1 (Positional i2), Bool)] -> [(i2, Int)]
interpretationT2 = allNumberValues . snd . digitValues
