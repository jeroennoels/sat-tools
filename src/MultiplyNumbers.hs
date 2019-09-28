{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module MultiplyNumbers where

import Formula
import Clauses
import Digits
import Numbers

import Data.Tuple (swap)
import Data.List (partition)


-- must be even
symN :: Int
symN = 4

halfN :: Int
halfN = div symN 2

delta1 :: [Int]
delta1 = [(-halfN)..halfN]

delta2 :: [Int]
delta2 = [(-halfN)..(halfN-1)]

shift :: (Int,Int) -> Int -> (Int,Int)
shift (a,b) c = (a+c, b+c)

inside :: (Int,Int) -> Bool
inside (a,b) = f a && f b where f x = elem x [0..symN]

snake :: Int -> [(Int,Int)]
snake k = let (a,b) = (symN-k, k)  -- a+b == symN
  in map (shift (a,b)) delta1 ++
     map (shift (a,b+1)) delta2

snakeSymmetrical :: Int -> [(Int,Int)]
snakeSymmetrical k = let s = snake k in s ++ map swap s

snakeInsideOut :: Int -> ([(Int,Int)], [(Int,Int)])
snakeInsideOut k = partition inside $ snakeSymmetrical k

--   (Ord j, IdentifyT1 i1 j, IdentifyT2 i2 j, SignSymmetric j) =>
--   Gensym i1 -> [i2] -> [i2] -> [i2] -> [Clause j]

biDiagonal :: Int -> [Positional (Char,Int)]
biDiagonal k = makeNumber ('D',k) (2 * symN)

zeroOutside :: (Ord i1, Ord i2) =>
    [(Int,Int)] -> i2 -> [Clause (T12 i1 (Positional i2))]
zeroOutside pairs diagonalId = concatMap (formulaToClauses . assertZero) pairs
  where
    assertZero (a,b) = zeroT2 (Positional diagonalId (a+b))
