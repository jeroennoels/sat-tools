{-# LANGUAGE ScopedTypeVariables #-}
module Tools where

import Formula
import Digits
import Addition

import Data.List (zipWith3, zipWith4)

type Gensym i = Int -> i

verifiedInputSize :: Int -> Int -> Int -> Int
verifiedInputSize a b c = if a == b && c == a+1
  then a else error "verifiedInputSize"

addNumbers :: forall i1 i2 j .
    (IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
    Gensym i1 -> [i2] -> [i2] -> [i2] -> Formula j
addNumbers g as bs cs = conjunction pairwise
  where
    n = verifiedInputSize (length as) (length bs) (length cs)
    gensyms0 = map g [0..(n-1)]
    gensyms1 = map g [n..(2*n-1)]
    pairwise = zipWith4 addDigitsT2 as bs gensyms1 gensyms0 :: [Formula j]
    wrong = zipWith3 addDigitsT1 gensyms0 gensyms1 cs :: [Formula j]

--   1 0 1 1    gensyms1
--     1 1 0 1  gensyms0
