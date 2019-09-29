{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module MultiplyNumbers where

import Formula
import Clauses
import Digits
import Numbers
import AddT1
import MultiplyT1

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

snakeInsideOut :: Int -> ([(Int,Int)], [(Int,Int)])
snakeInsideOut k = partition inside (snake k)


verifiedAsymmetricPair :: (Int,Int) -> (Int,Int)
verifiedAsymmetricPair (a,b) = if a > b
  then (a,b) else error "verifiedAsymmetricPair"


cell :: (Ord j, IdentifyT1 i1 j) =>
    Gensym i1 -> [i1] -> [i1] -> (Int,Int) -> (i1, [Clause j])
cell gensym xs ys (a,b) = let
  size = 2 * symN
  prod = gensym (a * size + b)
  formula = isValidT1 prod `And` multiplyDigits (xs !! a) (ys !! b) prod
  in (prod, formulaToClauses formula)


cellSumMirrors :: forall i1 i2 j . (Ord j, IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    Gensym i1 -> i2 -> [i1] -> [i1] -> (Int,Int) -> [Clause j]
cellSumMirrors gensym1 addTwoCells xs ys pair = let
  (a,b) = verifiedAsymmetricPair pair
  (g1, clauses1) = cell gensym1 xs ys (a,b)  -- a < b
  (g2, clauses2) = cell gensym1 xs ys (b,a)  -- mirror
  clauses = addDigitsT1 g1 g2 addTwoCells
  in clauses1 ++ clauses2 ++ clauses


-- input is LSFD
productsInside :: (Ord i1, Ord i2) => Gensym i1 ->
    [i1] -> [i1] -> i2 -> [(Int,Int)] -> [Clause (T12 i1 (Positional i2))]
productsInside gensym xs ys diagonalId pairs = concatMap forPair pairs
  where
    addTwoCells (a,b) = Positional diagonalId (a+b)
    forPair pair = cellSumMirrors gensym (addTwoCells pair) xs ys pair


zeroOutside :: (Ord i1, Ord i2) =>
    i2 -> [(Int,Int)] -> [Clause (T12 i1 (Positional i2))]
zeroOutside diagonalId pairs = concatMap forPair pairs
  where
    forPair (a,b) = formulaToClauses $ zeroT2 (Positional diagonalId (a+b))


as = map Number $ makeNumber 'a' (symN + 1)
bs = map Number $ makeNumber 'b' (symN + 1)

data Quux a b = GensymId a | Number (Positional b) 
  deriving (Eq, Ord, Read, Show)

getNumber :: Quux a b -> Maybe (Positional b)
getNumber (Number p) = Just p
getNumber _ = Nothing

type Chint = (Char, Int)
  
makeGensym :: Char -> Int -> Quux Chint a
makeGensym c n = GensymId (c,n) 

biDiagonal :: Int -> [Positional Chint]
biDiagonal k = makeNumber ('D',k) (2 * symN + 1)

snakeClauses :: Int -> [Clause (T12 (Quux Chint Char) (Positional Chint))]
snakeClauses k = validDiagonal ++ zeroOutside ('D',k) outside ++
  productsInside (makeGensym 'P') as bs ('D',k) inside 
  where
    validDiagonal = concatMap (formulaToClauses . isValidT2) (biDiagonal k)
    (inside, outside) = snakeInsideOut k

test = snakeClauses 0 ++ snakeClauses 1 ++ concatMap (formulaToClauses . isValidT1) (as ++ bs)

verifiedInput :: Int -> Int -> Int
verifiedInput lenX lenY = if lenX == lenY && lenX == 2 * symN
  then lenX else error "verifiedInput"
