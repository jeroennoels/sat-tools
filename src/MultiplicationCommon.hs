module MultiplicationCommon where

import Formula
import Clauses
import Digits
import Numbers
import MultiplyNumbers

type Label = String

type ClauseList = [Clause (T12 (CollectT1 Strint Label) (Positional Strint))]

-- By scalars we mean the basic unknown variables of the problem we want
-- to solve.  These are represented as fixed size T1 numbers because
-- of the limitations of our current implementation.
data Scalar = Scalar Label [CollectT1 Strint String]
  deriving (Eq, Ord, Read, Show)

-- experiment with bundling of variables and clauses
makeScalar :: Label -> (Scalar, ClauseList)
makeScalar label = (Scalar label as, clauses)
  where
    as = map Number $ makeNumber label (symN + 1)
    clauses = concatMap (formulaToClauses . isValidT1) as

zero :: ([Positional Strint], ClauseList)
zero = let
  zs = makeNumber ("zero", 0) (2 * symN + 5)
  clauses = concatMap formulaToClauses (map zeroT2 zs ++ map evenT2 zs)
  in (zs, clauses)

reverseNonNegativeT1 :: IdentifyT1 i j => [i] -> Formula j
reverseNonNegativeT1 [a] = posT1 a `Or` zeroT1 a
reverseNonNegativeT1 (a:as) = posT1 a `Or` (zeroT1 a `And` reverseNonNegativeT1 as)

isNonNegativeT1 :: [CollectT1 Strint Label] -> ClauseList
isNonNegativeT1 = formulaToClauses . reverseNonNegativeT1 . reverse

isNonNegativeScalar :: Scalar -> ClauseList
isNonNegativeScalar (Scalar _ quux) = isNonNegativeT1 quux

reversePositiveT1 :: IdentifyT1 i j => [i] -> Formula j
reversePositiveT1 [a] = posT1 a
reversePositiveT1 (a:as) = posT1 a `Or` (zeroT1 a `And` reversePositiveT1 as)

isPositiveT1 :: [CollectT1 Strint Label] -> ClauseList
isPositiveT1 = formulaToClauses . reversePositiveT1 . reverse

isPositiveScalar :: Scalar -> ClauseList
isPositiveScalar (Scalar _ quux) = isPositiveT1 quux

reversePositiveT2 :: IdentifyT2 i j => [i] -> Formula j
reversePositiveT2 [a] = posT2 a
reversePositiveT2 (a:as) = posT2 a `Or` (zeroT2 a `And` reversePositiveT2 as)

isPositiveT2 :: [Positional Strint] -> ClauseList
isPositiveT2 = formulaToClauses . reversePositiveT2 . reverse

reverseNonNegativeT2 :: IdentifyT2 i j => [i] -> Formula j
reverseNonNegativeT2 [a] = posT2 a `Or` zeroT2 a
reverseNonNegativeT2 (a:as) = posT2 a `Or` (zeroT2 a `And` reverseNonNegativeT2 as)

isNonNegativeT2 :: [Positional Strint] -> ClauseList
isNonNegativeT2 = formulaToClauses . reverseNonNegativeT2 . reverse


scalarIsZero :: Scalar -> ClauseList
scalarIsZero (Scalar _ a) = formulaToClauses (isZeroT1 a)

scalarIsOne :: Scalar -> ClauseList
scalarIsOne (Scalar _ a) = formulaToClauses (isOneT1 a)
