module Tools where

import Formula
import Clauses
import Eval

import Control.Applicative (liftA2)
import Data.Maybe

data Fine1 = Pos1 | Neg1 deriving (Eq, Ord, Show)
data Fine2 = Pos2 | Neg2 | Even2 deriving (Eq, Ord, Show)

data T12 i = T1 i Fine1
           | T2 i Fine2
           deriving (Eq, Ord, Show)

flipPosNeg :: T12 i -> T12 i
flipPosNeg (T1 i Pos1) = T1 i Neg1
flipPosNeg (T1 i Neg1) = T1 i Pos1
flipPosNeg (T2 i Pos2) = T2 i Neg2
flipPosNeg (T2 i Neg2) = T2 i Pos2
flipPosNeg x@(T2 _ Even2) = x

posT1 :: i -> Formula (T12 i)
posT1 i = Var (T1 i Pos1)

negT1 :: i -> Formula (T12 i)
negT1 i = Var (T1 i Neg1)

zeroT1 :: i -> Formula (T12 i)
zeroT1 i = Not (posT1 i) `And` Not (negT1 i)

isValidT1 :: i -> Formula (T12 i)
isValidT1 i = Not (posT1 i `And` negT1 i)

posT2 :: i -> Formula (T12 i)
posT2 i = Var (T2 i Pos2)

negT2 :: i -> Formula (T12 i)
negT2 i = Var (T2 i Neg2)

evenT2 :: i -> Formula (T12 i)
evenT2 i = Var (T2 i Even2)

oddT2 :: i -> Formula (T12 i)
oddT2 = Not . evenT2

zeroT2 :: i -> Formula (T12 i)
zeroT2 i = Not (posT2 i) `And` Not (negT2 i)

plusTwoT2 :: i -> Formula (T12 i)
plusTwoT2 i = evenT2 i `And` posT2 i

minusTwoT2 :: i -> Formula (T12 i)
minusTwoT2 i = evenT2 i `And` negT2 i

plusOneT2 :: i -> Formula (T12 i)
plusOneT2 i = oddT2 i `And` posT2 i

minusOneT2 :: i -> Formula (T12 i)
minusOneT2 i = oddT2 i `And` negT2 i

isValidT2 :: i -> Formula (T12 i)
isValidT2 i = Not (posT2 i `And` negT2 i) `And` (zeroT2 i `Implies` evenT2 i)

-- Exploit two symmetries: commutativity and flipping signs
addDigitsT2 :: i -> i -> i -> i -> Formula (T12 i)
addDigitsT2 a b x y = commute `And` fmap flipPosNeg commute
  where
    commute = quadrant a b x y `And` quadrant b a x y

quadrant :: i -> i -> i -> i -> Formula (T12 i)
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

addABXY :: [Clause (T12 Char)]
addABXY = formulaToClauses $ valid `And` addDigitsT2 'a' 'b' 'x' 'y'
  where
    valid = conjunction [isValidT2 'a', isValidT2 'b',
                         isValidT1 'x', isValidT1 'y']

-- A concrete variable assignment that represents one ternary digit
data DigitT1 = DigitT1 {isPos1 :: Bool, isNeg1 :: Bool}

getDigitT1 :: Eq i => Assignment (T12 i) -> i -> DigitT1
getDigitT1 a i = DigitT1 {
  isPos1 = assign a (T1 i Pos1),
  isNeg1 = assign a (T1 i Neg1)}

phi1 :: DigitT1 -> Maybe Int
phi1 (DigitT1 True False) = Just 1
phi1 (DigitT1 False True) = Just (-1)
phi1 (DigitT1 False False) = Just 0
phi1 (DigitT1 True True) = Nothing  -- forbidden


data DigitT2 = DigitT2 {isPos2 :: Bool, isNeg2 :: Bool, isEven2 :: Bool}

getDigitT2 :: Eq i => Assignment (T12 i) -> i -> DigitT2
getDigitT2 a i = DigitT2 {
  isPos2 = assign a (T2 i Pos2),
  isNeg2 = assign a (T2 i Neg2),
  isEven2 = assign a (T2 i Even2)}

phi2 :: DigitT2 -> Maybe Int
phi2 (DigitT2 True False True) = Just 2
phi2 (DigitT2 True False False) = Just 1
phi2 (DigitT2 False False True) = Just 0
phi2 (DigitT2 False True False) = Just (-1)
phi2 (DigitT2 False True True) = Just (-2)
phi2 _ = Nothing  -- forbidden

base3 :: Int -> Int -> Int
base3 x y = 3*x + y

referenceAdd :: DigitT2 -> DigitT2 -> DigitT1 -> DigitT1 -> Maybe Bool
referenceAdd a b x y = liftA2 (==)
   (liftA2 (+) (phi2 a) (phi2 b))
   (liftA2 base3 (phi1 x) (phi1 y))

testAddABXY :: Assignment (T12 Char) -> Bool
testAddABXY assignment = abxy == fromMaybe False ref
   where
     digit1 = getDigitT1 assignment
     digit2 = getDigitT2 assignment
     ref = referenceAdd (digit2 'a') (digit2 'b') (digit1 'x') (digit1 'y')
     abxy = evalClauses addABXY assignment

testAddDigitsT2 :: Bool
testAddDigitsT2 = all testAddABXY (allAssignments vars)
  where vars = distinctVariables addABXY


result :: [String]
result = ["Hello"]
