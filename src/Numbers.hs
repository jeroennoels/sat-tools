{-# LANGUAGE ScopedTypeVariables #-}
module Numbers where

import Formula
import Clauses
import Digits


type Gensym i = Int -> i

data Positional i = Positional i Int
  deriving (Eq, Ord, Read, Show)

idPositional :: Positional i -> i
idPositional (Positional i _) = i

makeNumber :: i -> Int -> [Positional i]
makeNumber i n = map (Positional i) [0..(n-1)]

equivalentNumbersT12 :: (IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    [i1] -> [i2] -> Formula j
equivalentNumbersT12 as bs = conjunction $ zipWith equivalentT12 as bs

integerEqualsNumberT1 :: (Ord i1, Ord i2) =>
    Integer -> [i1] -> [Clause (T12 i1 i2)]
integerEqualsNumberT1 x ab = concatMap formulaToClauses $
  zipWith intEqualsT1 (parseForT1 x ++ repeat 0) ab

-- Think carefully about the redundancy of the representation here. 
integerEqualsNumberT2 :: (Ord i1, Ord i2) =>
    Integer -> [i2] -> [Clause (T12 i1 i2)]
integerEqualsNumberT2 x ab = concatMap formulaToClauses $
  zipWith intEqualsT2 (parseForT1 x ++ repeat 0) ab


-- LSDF
parseForT1 :: Integer -> [Int]
parseForT1 x | x < 0 = map negate (parseForT1 (negate x))
parseForT1 x | x <= 1 = [fromIntegral x]
parseForT1 x = let
  (q,r) = quotRem x 3
  (v,w) = if r <= 1 then (q,r) else (q+1, r-3)
  in fromIntegral w : parseForT1 v


nonZeroNumberT1 :: (Ord i1, Ord i2) => [i1] -> [Clause (T12 i1 i2)]
nonZeroNumberT1 as = formulaToClauses $ disjunction $
  map Not (zipWith intEqualsT1 (repeat 0) as)
