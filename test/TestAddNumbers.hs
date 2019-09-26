{-# LANGUAGE ScopedTypeVariables #-}
module TestAddNumbers where

import Formula
import Clauses
import Eval
import Digits
import DigitAssignment
import AddNumbers

import Data.Maybe
import Data.List.Split (chunksOf)
import Control.Applicative (liftA2)
import Data.Set (Set)
import qualified Data.Set as Set


carryT4 :: Int -> (Int, Int)
carryT4 4 = (1,1)
carryT4 3 = (1,0)
carryT4 2 = (1,-1)
carryT4 1 = (0,1)
carryT4 0 = (0,0)
carryT4 k = (-a,-b) where (a,b) = carryT4 (-k)  -- symmetry


referenceAddNumbers :: [DigitT2] -> [DigitT2] -> [DigitT2] -> Maybe Bool
referenceAddNumbers [a',b'] [c',d'] [x',y',z'] =
  let mabyeInts = sequence $ map phi2 [a',b',c',d',x',y',z']
  in if isNothing mabyeInts
     then Nothing
     else let Just [a,b,c,d,x,y,z] = mabyeInts
              (car, lsd) = carryT4 (a + c)
              (msd, rem) = carryT4 (b + d)
          in Just $ [lsd, car + rem, msd] == [x,y,z]


-- Quick hack for exploration and basic testing.
charGensym :: Gensym Char
charGensym = (!!) ['A'..'Z']

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


testAddNumbers :: Bool
testAddNumbers = all (testAddSmallNumbers dummies distinct) power
  where
    distinct = distinctVariables addSmallNumbers
    (dummies, inputs) = Set.partition isDummy distinct
    power = Set.toList $ Set.powerSet inputs
    isDummy :: CharId -> Bool
    isDummy (T2 _ _) = False
    isDummy (T1 _ _) = True


nn :: Int
nn = 3

as = map (Positional 'a') [0..(nn-1)]
bs = map (Positional 'b') [0..(nn-1)]
cs = map (Positional 'c') [0..nn]

intGensym :: Char -> Gensym (Char, Int)
intGensym = (,)

addition :: [Clause (T12 (Char, Int) (Positional Char))]
addition = concatMap (formulaToClauses . isValidT2) (as ++ bs ++ cs)
        ++ addNumbers (intGensym 'G') as bs cs
