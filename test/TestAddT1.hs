{-# LANGUAGE ScopedTypeVariables #-}
module TestAddT1 (testAddDigitsT1) where

import Formula
import Clauses
import Eval
import Digits
import DigitAssignment
import AddT1

import Control.Applicative (liftA2)
import Data.Maybe


addABX :: [Clause CharId]
addABX = concatMap formulaToClauses valid ++ addDigitsT1 'a' 'b' 'x'
  where
    valid = [isValidT1 'a', isValidT1 'b', isValidT2 'x']

referenceAddT1 :: DigitT1 -> DigitT1 -> DigitT2 -> Maybe Bool
referenceAddT1 a b x = liftA2 (+) (phi1 a) (phi1 b) === phi2 x
  where (===) = liftA2 (==)

testAddABX :: Assignment CharId -> Bool
testAddABX assignment = abx == fromMaybe False ref
   where
     digit1 = getDigitT1 assignment
     digit2 = getDigitT2 assignment
     ref = referenceAddT1 (digit1 'a') (digit1 'b') (digit2 'x')
     abx = evalClauses addABX assignment

testAddDigitsT1 :: Bool
testAddDigitsT1 = all testAddABX (allAssignments vars)
  where vars = distinctVariables addABX
