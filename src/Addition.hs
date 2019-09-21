module Addition where

import Formula
import Clauses
import Eval
import Digits

import Control.Applicative (liftA2)
import Data.Maybe

-- Exploit two symmetries: commutativity and flipping signs
addDigitsT2 :: (IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
    i2 -> i2 -> i1 -> i1 -> Formula j
addDigitsT2 a b x y = commute `And` fmap flipPosNeg commute
  where
    commute = quadrant a b x y `And`
              quadrant b a x y

quadrant :: (IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    i2 -> i2 -> i1 -> i1 -> Formula j
quadrant a b x y = conjunction [
  (plusTwoT2 a `And` plusTwoT2 b)         -- 2 + 2
  `Implies` (posT1 x `And` posT1 y),      -- becomes (1,1)
  (plusTwoT2 a `And` plusOneT2 b)         -- 2 + 1
  `Implies` (posT1 x `And` zeroT1 y),     -- becomes (1,0)
  ((plusTwoT2 a `And` zeroT2 b) `Or`      -- 2 + 0
   (plusOneT2 a `And` plusOneT2 b))       -- 1 + 1
  `Implies` (posT1 x `And` negT1 y),      -- becomes (1,-1)
  ((plusTwoT2 a `And` minusOneT2 b) `Or`  -- 2 + (-1)
   (plusOneT2 a `And` zeroT2 b))          -- 1 + 0
  `Implies` (zeroT1 x `And` posT1 y),     -- becomes (0,1)
  ((plusTwoT2 a `And` minusTwoT2 b) `Or`  -- 2 + (-2)
   (plusOneT2 a `And` minusOneT2 b) `Or`  -- 1 + (-1)
   (zeroT2 a `And` zeroT2 b))             -- 0 + 0
  `Implies` (zeroT1 x `And` zeroT1 y)]    -- becomes (0,0)

addABXY :: [Clause (T12 Char Char)]
addABXY = formulaToClauses $ valid `And` addDigitsT2 'a' 'b' 'x' 'y'
  where
    valid = conjunction [isValidT2 'a', isValidT2 'b',
                         isValidT1 'x', isValidT1 'y']

base3 :: Int -> Int -> Int
base3 x y = 3*x + y

referenceAdd :: DigitT2 -> DigitT2 -> DigitT1 -> DigitT1 -> Maybe Bool
referenceAdd a b x y = liftA2 (==)
   (liftA2 (+) (phi2 a) (phi2 b))
   (liftA2 base3 (phi1 x) (phi1 y))

testAddABXY :: Assignment (T12 Char Char) -> Bool
testAddABXY assignment = abxy == fromMaybe False ref
   where
     digit1 = getDigitT1 assignment
     digit2 = getDigitT2 assignment
     ref = referenceAdd (digit2 'a') (digit2 'b') (digit1 'x') (digit1 'y')
     abxy = evalClauses addABXY assignment

testAddDigitsT2 :: Bool
testAddDigitsT2 = all testAddABXY (allAssignments vars)
  where vars = distinctVariables addABXY


addDigitsT1 :: (IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
    i1 -> i1 -> i2 -> Formula j
addDigitsT1 a b x = commute `And` fmap flipPosNeg commute
  where commute  = quadrantT1 a b x `And` quadrantT1 b a x

quadrantT1 :: (IdentifyT1 i1 j, IdentifyT2 i2 j) => i1 -> i1 -> i2 -> Formula j
quadrantT1 a b x = conjunction [
  (posT1 a `And` posT1 b)   `Implies` plusTwoT2 x,  -- 1+1 = 2
  (posT1 a `And` zeroT1 b)  `Implies` plusOneT2 x,  -- 1+0 = 1
  (posT1 a `And` negT1 b)   `Implies` zeroT2 x,     -- 1-1 = 0
  (zeroT1 a `And` zeroT1 b) `Implies` zeroT2 x]     -- 0+0 = 0

addABX :: [Clause (T12 Char Char)]
addABX = formulaToClauses $ valid `And` addDigitsT1 'a' 'b' 'x'
  where
    valid = conjunction [isValidT1 'a', isValidT1 'b', isValidT2 'x']

referenceAddT1 :: DigitT1 -> DigitT1 -> DigitT2 -> Maybe Bool
referenceAddT1 a b x = liftA2 (+) (phi1 a) (phi1 b) === phi2 x
  where (===) = liftA2 (==)

testAddABX :: Assignment (T12 Char Char) -> Bool
testAddABX assignment = abx == fromMaybe False ref
   where
     digit1 = getDigitT1 assignment
     digit2 = getDigitT2 assignment
     ref = referenceAddT1 (digit1 'a') (digit1 'b') (digit2 'x')
     abx = evalClauses addABX assignment

testAddDigitsT1 :: Bool
testAddDigitsT1 = all testAddABX (allAssignments vars)
  where vars = distinctVariables addABX
