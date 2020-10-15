{-# LANGUAGE ScopedTypeVariables #-}
module AddNumbers (addNumbers, subtractNumbers, Gensym) where

import Formula
import Clauses
import Digits
import Numbers
import AddT1
import AddT2

import Data.List (zipWith3, zipWith4)

verifiedInputSize :: Int -> Int -> Int -> Int
verifiedInputSize a b c = if a == b && c == a+1
  then a else error "verifiedInputSize"

addOrSubtractNumbers :: forall i1 i2 j .
    (Ord j, IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    (i2 -> i2 -> i1 -> i1 -> [Clause j]) ->
    Gensym i1 -> [i2] -> [i2] -> [i2] -> [Clause j]
addOrSubtractNumbers operationT2 makeGensym as bs cs = let
  n = verifiedInputSize (length as) (length bs) (length cs)
  gensyms0 = map makeGensym [0..(n-1)]
  gensyms1 = map makeGensym [n..(2*n-1)]  -- carry
  cs' = init (tail cs)
  valid = map isValidT1 (gensyms0 ++ gensyms1) :: [Formula j]
  lsd = equivalentT12 (head gensyms0) (head cs) :: Formula j
  msd = equivalentT12 (last gensyms1) (last cs) :: Formula j
  pairwise = zipWith4 operationT2 as bs gensyms1 gensyms0 :: [[Clause j]]
  middle :: [[Clause j]]
  middle = zipWith3 addDigitsT1 (tail gensyms0) (init gensyms1) cs'
  in concatMap formulaToClauses (lsd : msd: valid) ++ concat (pairwise ++ middle)


addNumbers :: forall i1 i2 j .
    (Ord j, IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    Gensym i1 -> [i2] -> [i2] -> [i2] -> [Clause j]
addNumbers = addOrSubtractNumbers addDigitsT2


subtractNumbers :: forall i1 i2 j .
    (Ord j, IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    Gensym i1 -> [i2] -> [i2] -> [i2] -> [Clause j]
subtractNumbers = addOrSubtractNumbers subtractDigitsT2
