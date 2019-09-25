module TestMultiplyT1 (testMultiply) where

import Formula
import Eval
import Clauses
import Digits
import MultiplyT1

import Control.Applicative (liftA2)
import Data.Maybe


-- Expressing digits a,b and c with a * b = c
multiplyABC :: [Clause CharId]
multiplyABC = formulaToClauses $ abcDigits `And` multiplyDigits 'a' 'b' 'c'
  where
    abcDigits = conjunction $ map isValidT1 "abc"

referenceMultiply :: DigitT1 -> DigitT1 -> DigitT1 -> Maybe Bool
referenceMultiply a b c = liftA2 (==) (liftA2 (*) (phi1 a) (phi1 b)) (phi1 c)

testMultiplyABC :: Assignment CharId -> Bool
testMultiplyABC assignment = abc == fromMaybe False ref
   where
     digit = getDigitT1 assignment
     ref = referenceMultiply (digit 'a') (digit 'b') (digit 'c')
     abc = evalClauses multiplyABC assignment

testMultiply :: Bool
testMultiply = and $ map testMultiplyABC $ allAssignments vars
  where vars = distinctVariables multiplyABC
