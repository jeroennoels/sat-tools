module Tools where

import Formula
import Clauses
import Eval

import Control.Applicative (liftA2)
import Data.Maybe

data Fine1 = PP | MM deriving (Eq, Ord, Show)
data Fine2 = P2 | M2 | E2 deriving (Eq, Ord, Show)

data T21 i = T2 i Fine2
           | T1 i Fine1
           deriving (Eq, Ord, Show)

plus1 :: i -> Formula (T21 i)
plus1 i = Var (T1 i PP)

mins1 :: i -> Formula (T21 i)
mins1 i = Var (T1 i MM)

zero1 :: i -> Formula (T21 i)
zero1 i = Not (plus1 i) `And` Not (mins1 i)

plus2 :: i -> Formula (T21 i)
plus2 i = Var (T2 i P2)

mins2 :: i -> Formula (T21 i)
mins2 i = Var (T2 i M2)

even2 :: i -> Formula (T21 i)
even2 i = Var (T2 i E2)

odd2 :: i -> Formula (T21 i)
odd2 = Not . even2

pTwo2 :: i -> Formula (T21 i)
pTwo2 i = even2 i `And` plus2 i

mTwo2 :: i -> Formula (T21 i)
mTwo2 i = even2 i `And` mins2 i

pOne2 :: i -> Formula (T21 i)
pOne2 i = odd2 i `And` plus2 i

mOne2 :: i -> Formula (T21 i)
mOne2 i = odd2 i `And` mins2 i

zero2 :: i -> Formula (T21 i)
zero2 i = Not (plus2 i) `And` Not (mins2 i)

isValidT1 :: i -> Formula (T21 i)
isValidT1 i = Not (plus1 i `And` mins1 i)

isValidT2 :: i -> Formula (T21 i)
isValidT2 i = Not (plus2 i `And` mins2 i) `And` (zero2 i `Implies` even2 i)

pareq :: i -> i -> Formula (T21 i)
pareq aa bb = even2 aa `Equiv` even2 bb 

parop :: i -> i -> Formula (T21 i)
parop aa bb = even2 aa `Equiv` odd2 bb 

addT2 :: i -> i -> i -> i -> Formula (T21 i)
addT2 aa bb c d =
  -- 2+2 <=> (1,1)
  ((pTwo2 aa `And` pTwo2 bb) `Equiv` (plus1 c `And` plus1 d)) `And`
  ((mTwo2 aa `And` mTwo2 bb) `Equiv` (mins1 c `And` mins1 d)) `And`
  -- 2+1 1+2 <=> (1,0)
  (((plus2 aa `And` plus2 bb) `And` parop aa bb)
    `Equiv` (plus1 c `And` zero1 d)) `And`
  (((mins2 aa `And` mins2 bb) `And` parop aa bb)
    `Equiv` (mins1 c `And` zero1 d)) `And`
  -- 2+0 1+1 0+2 <=> (1,-1)
  (((pTwo2 aa `And` zero2 bb)
        `Or` (zero2 aa `And` pTwo2 bb)
        `Or` (pOne2 aa `And` pOne2 bb)) 
    `Equiv` (plus1 c `And` mins1 d)) `And`
  (((mTwo2 aa `And` zero2 bb)
        `Or` (zero2 aa `And` mTwo2 bb)
        `Or` (mOne2 aa `And` mOne2 bb)) 
    `Equiv` (mins1 c `And` plus1 d)) `And`
  -- 2+(-1) -1+2<=> (0,1)
  -- 1+0 0+1 <=> (0,1)
  (((pTwo2 aa `And` mOne2 bb) `Or` (mOne2 aa `And` pTwo2 bb) `Or`
    (pOne2 aa `And` zero2 bb) `Or` (zero2 aa `And` pOne2 bb))
    `Equiv` (zero1 c `And` plus1 d)) `And`
  (((mTwo2 aa `And` pOne2 bb) `Or` (pOne2 aa `And` mTwo2 bb) `Or`
    (mOne2 aa `And` zero2 bb) `Or` (zero2 aa `And` mOne2 bb))
    `Equiv` (zero1 c `And` mins1 d)) `And`
  -- 2+(-2) 1+(-1) 0+0 ... <=> (0,0)
  (((((plus2 aa `And` mins2 bb) `Or` (mins2 aa `And` plus2 bb))
        `And` pareq aa bb)
      `Or` (zero2 aa `And` zero2 bb))
    `Equiv` (zero1 c `And` zero1 d)) 

addABXY :: [Clause (T21 Char)]
addABXY = formulaToClauses $ valid `And` addT2 'a' 'b' 'x' 'y'
  where
    valid = isValidT2 'a' `And` isValidT2 'b' `And`
            isValidT1 'x' `And` isValidT1 'y'


-- A concrete variable assignment that represents one ternary digit
data DigitT1 = DigitT1 {isPP :: Bool, isMM :: Bool}

getDigitT1 :: Eq i => Assignment (T21 i) -> i -> DigitT1
getDigitT1 a i = DigitT1 {
  isPP = assign a (T1 i PP),
  isMM = assign a (T1 i MM)}

phi1 :: DigitT1 -> Maybe Int
phi1 (DigitT1 True False) = Just 1
phi1 (DigitT1 False True) = Just (-1)
phi1 (DigitT1 False False) = Just 0
phi1 (DigitT1 True True) = Nothing  -- forbidden


data DigitT2 = DigitT2 {isP2 :: Bool, isM2 :: Bool, isE2 :: Bool}

getDigitT2 :: Eq i => Assignment (T21 i) -> i -> DigitT2
getDigitT2 a i = DigitT2 {
  isP2 = assign a (T2 i P2),
  isM2 = assign a (T2 i M2),
  isE2 = assign a (T2 i E2)}

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
referenceAdd a b c d = liftA2 (==)
   (liftA2 (+) (phi2 a) (phi2 b))
   (liftA2 base3 (phi1 c) (phi1 d))


testAddABXY :: Assignment (T21 Char) -> Bool
testAddABXY assignment = abxy == fromMaybe False ref
   where
     digit1 = getDigitT1 assignment
     digit2 = getDigitT2 assignment
     ref = referenceAdd (digit2 'a') (digit2 'b') (digit1 'x') (digit1 'y')
     abxy = evalClauses addABXY assignment

--testMultiply :: Bool
testAdd = filter (not . testAddABXY) $ allAssignments vars
  where vars = distinctVariables addABXY


result :: [String]
result = ["Hello"]

