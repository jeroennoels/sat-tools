{-# LANGUAGE ScopedTypeVariables #-}
module AddNumbers (addNumbers, Gensym) where

import Formula
import Clauses
import Digits
import AddT1
import AddT2

import Data.List (zipWith3, zipWith4)


type Gensym i = Int -> i

verifiedInputSize :: Int -> Int -> Int -> Int
verifiedInputSize a b c = if a == b && c == a+1
  then a else error "verifiedInputSize"

addNumbers :: forall i1 i2 j .
    (Ord j, IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
    Gensym i1 -> [i2] -> [i2] -> [i2] -> [Clause j]
addNumbers makeGensym as bs cs = let
  n = verifiedInputSize (length as) (length bs) (length cs)
  gensyms0 = map makeGensym [0..(n-1)]
  gensyms1 = map makeGensym [n..(2*n-1)]  -- carry
  cs' = init (tail cs)
  valid = map isValidT1 (gensyms0 ++ gensyms1) :: [Formula j]
  lsd = equivalentT12 (head gensyms0) (head cs) :: Formula j
  msd = equivalentT12 (last gensyms1) (last cs) :: Formula j
  pairwise = zipWith4 addDigitsT2 as bs gensyms1 gensyms0 :: [[Clause j]]
  middle :: [Formula j]
  middle = zipWith3 addDigitsT1 (tail gensyms0) (init gensyms1) cs'
  in concatMap formulaToClauses (valid ++ lsd : msd : middle) ++ concat pairwise
