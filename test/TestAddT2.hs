{-# LANGUAGE ScopedTypeVariables #-}
module TestAddT2 (addABXY, testAddDigitsT2) where

import Formula
import Clauses
import Eval
import Digits
import AddT2

import Control.Applicative (liftA2)
import Data.Maybe


addABXY :: [Clause CharId]
addABXY = concatMap formulaToClauses valid ++ addition
  where
    addition = addDigitsT2 'a' 'b' 'x' 'y'
    valid :: [Formula CharId]
    valid = [isValidT2 'a', isValidT2 'b', isValidT1 'x', isValidT1 'y']

base3 :: Int -> Int -> Int
base3 x y = 3*x + y

referenceAdd :: DigitT2 -> DigitT2 -> DigitT1 -> DigitT1 -> Maybe Bool
referenceAdd a b x y = liftA2 (==)
   (liftA2 (+) (phi2 a) (phi2 b))
   (liftA2 base3 (phi1 x) (phi1 y))

testAddABXY :: Assignment CharId -> Bool
testAddABXY assignment = abxy == fromMaybe False ref
   where
     digit1 = getDigitT1 assignment
     digit2 = getDigitT2 assignment
     ref = referenceAdd (digit2 'a') (digit2 'b') (digit1 'x') (digit1 'y')
     abxy = evalClauses addABXY assignment

testAddDigitsT2 :: Bool
testAddDigitsT2 = all testAddABXY (allAssignments vars)
  where vars = distinctVariables addABXY
