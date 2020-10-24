{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
module Model where

import Digits
import Numbers
import DigitAssignment

import Data.Maybe (fromJust, mapMaybe)
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

numberValue :: Eq i => [DigitValue (Positional i)] -> (i, Integer)
numberValue ds = (id, sum (map term ds))
  where
    [id] = nub (map idDigitValue ds)
    term (DigitValue (Positional _ k) a) = fromIntegral a * 3^k

allNumberValues :: Eq i => [DigitValue (Positional i)] -> [(i, Integer)]
allNumberValues = map numberValue . groupBy ((==) `on` idDigitValue)


interpretationT1 :: forall i1 i2 i .
    (Eq i1, Eq i2, Ord i, Ord i1, Ord i2, Show i, Show i1, Show i2) =>
    (i1 -> Maybe (Positional i)) -> [(T12 i1 i2, Bool)] -> [(i, Integer)]
interpretationT1 pos = allNumberValues . fst . digitValues . mapMaybe extract
  where
    extract :: (T12 i1 i2, Bool) -> Maybe (T12 (Positional i) i2, Bool)
    extract = maybeFirst (numberT1 pos)


-- TODO eliminate copy/paste code
interpretationT2 :: forall i1 i2 i .
    (Eq i1, Eq i2, Ord i, Ord i1, Ord i2, Show i, Show i1, Show i2) =>
    (i2 -> Maybe (Positional i)) -> [(T12 i1 i2, Bool)] -> [(i, Integer)]
interpretationT2 pos = allNumberValues . snd . digitValues . mapMaybe extract
  where
    extract :: (T12 i1 i2, Bool) -> Maybe (T12 i1 (Positional i), Bool)
    extract = maybeFirst (numberT2 pos)

dummyInterpretationT2 :: forall i1 i2 i .
    (Eq i1, Eq i2, Ord i, Ord i1, Ord i2, Show i, Show i1, Show i2) =>
    (i2 -> Maybe (Positional i)) -> [(T12 i1 i2, Bool)] -> [(i, Integer)]
dummyInterpretationT2 _ _ = []

maybeFirst :: (a -> Maybe b) -> (a,c) -> Maybe (b,c)
maybeFirst f (a,c) = (,c) `fmap` f a


numberT1 :: (i1 -> Maybe (Positional i)) ->
    T12 i1 i2 -> Maybe (T12 (Positional i) i2)
numberT1 f (T1 i a) = flip T1 a `fmap` f i
numberT1 _ (T2 _ _) = Nothing


numberT2 :: (i2 -> Maybe (Positional i)) ->
    T12 i1 i2 -> Maybe (T12 i1 (Positional i))
numberT2 f (T2 i a) = flip T2 a `fmap` f i
numberT2 _ (T1 _ _) = Nothing
