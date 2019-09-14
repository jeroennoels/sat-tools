module Arithmetic where

import Formula
import Eval
import Clauses

import Control.Applicative (liftA2)
import Data.Maybe

-- Plus or Minus
data Sign i = P1 i | M1 i deriving (Eq, Ord, Show)

plus :: i -> Formula (Sign i)
plus v = Var (P1 v)

mins :: i -> Formula (Sign i)
mins v = Var (M1 v)

-- The sign of a ternary digit cannot simultaneously be plus and minus.
isDigit :: i -> Formula (Sign i)
isDigit v = Not (plus v `And` mins v)

multiplyDigits :: i -> i -> i -> Formula (Sign i)
multiplyDigits a b c =
  (((plus a `And` plus b) `Or` (mins a `And` mins b)) `Equiv` plus c) `And`
  (((plus a `And` mins b) `Or` (mins a `And` plus b)) `Equiv` mins c)

-- A concrete variable assignment that represents one ternary digit
data Digit1 = Digit1 {isP1 :: Bool, isM1 :: Bool}

getDigit1 :: Eq i => Assignment (Sign i) -> i -> Digit1
getDigit1 a i = Digit1 {
  isP1 = assign a (P1 i),
  isM1 = assign a (M1 i)}

phi1 :: Digit1 -> Maybe Int
phi1 (Digit1 True False) = Just 1
phi1 (Digit1 False True) = Just (-1)
phi1 (Digit1 False False) = Just 0
phi1 (Digit1 True True) = Nothing  -- forbidden

-- Expressing digits a,b and c with a * b = c
multiplyABC :: [Clause (Sign Char)]
multiplyABC = formulaToClauses $ abcDigits `And` multiplyDigits 'a' 'b' 'c'
  where
    abcDigits = isDigit 'a' `And` isDigit 'b' `And` isDigit 'c'

referenceMultiply :: Digit1 -> Digit1 -> Digit1 -> Maybe Bool
referenceMultiply a b c = liftA2 (==) (liftA2 (*) (phi1 a) (phi1 b)) (phi1 c)

testMultiplyABC :: Assignment (Sign Char) -> Bool
testMultiplyABC assignment = abc == fromMaybe False ref
   where
     digit = getDigit1 assignment
     ref = referenceMultiply (digit 'a') (digit 'b') (digit 'c')
     abc = evalClauses multiplyABC assignment

testMultiply :: Bool
testMultiply = and $ map testMultiplyABC $ allAssignments vars
  where vars = distinctVariables multiplyABC
