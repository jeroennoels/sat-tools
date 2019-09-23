{-# LANGUAGE ScopedTypeVariables #-}
module Tools where

import Formula
import Clauses
import Eval
import Digits
import Addition

import Data.Maybe
import Data.List (zipWith3, zipWith4)
import Control.Applicative (liftA2)
import qualified Data.Set as Set

type Gensym i = Int -> i

verifiedInputSize :: Int -> Int -> Int -> Int
verifiedInputSize a b c = if a == b && c == a+1
  then a else error "verifiedInputSize"

addNumbers :: forall i1 i2 j .
    (IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
    Gensym i1 -> [i2] -> [i2] -> [i2] -> Formula j
addNumbers makeGensym as bs cs = conjunction $
  valid ++ pairwise ++ lsd : msd : middle
  where
    n = verifiedInputSize (length as) (length bs) (length cs)
    gensyms0 = map makeGensym [0..(n-1)]
    gensyms1 = map makeGensym [n..(2*n-1)]  -- carry
    cs' = init (tail cs)
    valid = map isValidT1 (gensyms0 ++ gensyms1) :: [Formula j]
    lsd = equivalentT12 (head gensyms0) (head cs) :: Formula j
    msd = equivalentT12 (last gensyms1) (last cs) :: Formula j
    pairwise = zipWith4 addDigitsT2 as bs gensyms1 gensyms0 :: [Formula j]
    middle :: [Formula j]
    middle = zipWith3 addDigitsT1 (tail gensyms0) (init gensyms1) cs'


referenceAddNumbers :: [DigitT2] -> [DigitT2] -> [DigitT2] -> Maybe Bool
referenceAddNumbers as bs cs = liftA2 (==)
  (liftA2 (+) (phi2Base3 as) (phi2Base3 bs))
  (phi2Base3 cs)

-- quick hack for exploration only
charGensym :: Gensym Char
charGensym = (!!) ['A'..'Z']

addSmallNumbers :: [Clause (T12 Char Char)]
addSmallNumbers = formulaToClauses $
    valid `And` addNumbers charGensym ['a','b'] ['c','d'] ['x','y','z']
  where
    valid = conjunction $ map isValidT2 ['a','b','c','d','x','y','z']

testAddSmallNumbers :: Assignment (T12 Char Char) -> Bool
testAddSmallNumbers assignment = evaluated == fromMaybe False ref
   where
     digit = getDigitT2 assignment
     ref = referenceAddNumbers
             [digit 'a', digit 'b']
             [digit 'c', digit 'd']
             [digit 'x', digit 'y', digit 'y']
     evaluated = evalClauses addSmallNumbers assignment

-- quick hack for exploration only
notGensym :: T12 Char Char -> Bool
notGensym (T2 _ _) = True
notGensym (T1 _ _) = False

testAddNumbers :: Bool
testAddNumbers = all testAddSmallNumbers (allAssignments vars)
  where vars = Set.filter notGensym (distinctVariables addSmallNumbers)
