module Arithmetic where

import Formula
import Eval
import Clauses
import Digits

import Control.Applicative (liftA2)
import Data.Maybe


multiplyDigits :: IdentifyT1 i j => i -> i -> i -> Formula j
multiplyDigits a b c =
  (((posT1 a `And` posT1 b) `Or` (negT1 a `And` negT1 b)) `Implies` posT1 c) `And`
  (((posT1 a `And` negT1 b) `Or` (negT1 a `And` posT1 b)) `Implies` negT1 c) `And`
  ((zeroT1 a `Or` zeroT1 b) `Implies` zeroT1 c)


-- Expressing digits a,b and c with a * b = c
multiplyABC :: [Clause (T12 Char Char)]
multiplyABC = formulaToClauses $ abcDigits `And` multiplyDigits 'a' 'b' 'c'
  where
    abcDigits = conjunction $ map isValidT1 "abc"

referenceMultiply :: DigitT1 -> DigitT1 -> DigitT1 -> Maybe Bool
referenceMultiply a b c = liftA2 (==) (liftA2 (*) (phi1 a) (phi1 b)) (phi1 c)

testMultiplyABC :: Assignment (T12 Char Char) -> Bool
testMultiplyABC assignment = abc == fromMaybe False ref
   where
     digit = getDigitT1 assignment
     ref = referenceMultiply (digit 'a') (digit 'b') (digit 'c')
     abc = evalClauses multiplyABC assignment

testMultiply :: Bool
testMultiply = and $ map testMultiplyABC $ allAssignments vars
  where vars = distinctVariables multiplyABC
