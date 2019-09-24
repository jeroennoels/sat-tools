{-# LANGUAGE ScopedTypeVariables #-}
module Tools where

import Formula
import Clauses
import Eval
import Digits
import Addition

import Data.Maybe
import Data.List.Split (chunksOf)
import Data.List (zipWith3, zipWith4)
import Control.Applicative (liftA2)
import Data.Set (Set)
import qualified Data.Set as Set

type Gensym i = Int -> i

verifiedInputSize :: Int -> Int -> Int -> Int
verifiedInputSize a b c = if a == b && c == a+1
  then a else error "verifiedInputSize"

addNumbers :: forall i1 i2 j .
    (Ord j, IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
    Gensym i1 -> [i2] -> [i2] -> [i2] -> [Clause j]
addNumbers makeGensym as bs cs = let
  n = verifiedInputSize (length as) (length bs) (length cs)
  gensyms0 = map makeGensym [0..(n-1)]
  gensyms1 = map makeGensym [n..(2*n-1)]  -- carry
  cs' = init (tail cs)
  valid = map isValidT1 (gensyms0 ++ gensyms1) :: [Formula j]
  lsd = equivalentT12 (head gensyms0) (head cs) :: Formula j
  msd = equivalentT12 (last gensyms1) (last cs) :: Formula j
  pairwise = zipWith4 addDigitsT2_compiled as bs gensyms1 gensyms0 :: [[Clause j]]
  middle :: [Formula j]
  middle = zipWith3 addDigitsT1 (tail gensyms0) (init gensyms1) cs'
  in concatMap formulaToClauses (valid ++ lsd : msd : middle) ++ concat pairwise

carryT4 :: Int -> (Int, Int)
carryT4 4 = (1,1)
carryT4 3 = (1,0)
carryT4 2 = (1,-1)
carryT4 1 = (0,1)
carryT4 0 = (0,0)
carryT4 k = (-a,-b) where (a,b) = carryT4 (-k)

referenceAddNumbers :: [DigitT2] -> [DigitT2] -> [DigitT2] -> Maybe Bool
referenceAddNumbers [aa,bb] [cc,dd] [xx,yy,zz] =
  let mabyeInts = sequence $ map phi2 [aa,bb,cc,dd,xx,yy,zz]
  in if isNothing mabyeInts
     then Nothing
     else let Just [a,b,c,d,x,y,z] = mabyeInts
              (car, lsd) = carryT4 (a + c)
              (msd, rem) = carryT4 (b + d)
          in Just $ [lsd, car + rem, msd] == [x,y,z]

-- Quick hack for exploration and basic testing.
charGensym :: Gensym Char
charGensym = (!!) ['A'..'Z']

type CharId = T12 Char Char

addSmallNumbers :: [Clause CharId]
addSmallNumbers = formulaToClauses valid ++
    addNumbers charGensym ['a','b'] ['c','d'] ['x','y','z']
  where
    valid = conjunction $ map isValidT2 ['a','b','c','d','x','y','z']

testAddSmallNumbers :: Set CharId -> Set CharId -> Set CharId -> Bool
testAddSmallNumbers dummies variables trueInputs = let
  inputAssignment = characteristic variables trueInputs :: Assignment CharId
  setsOfDummies = Set.toList $ Set.powerSet dummies :: [Set CharId]
  quux = map (Set.union trueInputs) setsOfDummies :: [Set CharId]
  assignments = map (characteristic variables) quux :: [Assignment CharId]
  digit = getDigitT2 inputAssignment :: Char -> DigitT2
  ref = referenceAddNumbers
          [digit 'a', digit 'b']
          [digit 'c', digit 'd']
          [digit 'x', digit 'y', digit 'z']
  satisfiable = any (evalClauses addSmallNumbers) assignments
  in satisfiable == fromMaybe False ref

-- quick hack for exploration only
isDummy :: T12 Char Char -> Bool
isDummy (T2 _ _) = False
isDummy (T1 _ _) = True

falseIsError :: Bool -> Bool
falseIsError True = True
falseIsError False = error "Fail!"

--testAddNumbers :: Bool
testAddNumbers = map
  (falseIsError . all (testAddSmallNumbers dummies distinct)) chunked
  where
    chunked = chunksOf 1000 pow
    pow = Set.toList $ Set.powerSet inputs
    distinct = distinctVariables addSmallNumbers
    (dummies, inputs) = Set.partition isDummy distinct
