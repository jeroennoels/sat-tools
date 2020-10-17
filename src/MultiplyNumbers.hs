{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module MultiplyNumbers where

import Formula
import Clauses
import Digits
import Numbers
import AddT1
import AddNumbers
import MultiplyT1

import Data.Tuple (swap)
import Data.List (partition)
import Data.Maybe

-- This is all very ad hoc at the moment.  In some places, the number of digits
-- is still hardwired in the implementation.
-- We shall multiply two T1-represented numbers of (symN + 1) digits.
-- The result will be a T2-represented number of (2 * symN + 3) digits.

-- must be even
symN :: Int
symN = 6

shift :: (Int,Int) -> Int -> (Int,Int)
shift (a,b) c = (a+c, b+c)

inside :: (Int,Int) -> Bool
inside (a,b) = f a && f b where f x = elem x [0..symN]

snake :: Int -> [(Int,Int)]
snake k = let (a,b) = (symN-k, k)  -- a+b == symN
  in map (shift (a,b)) delta1 ++
     map (shift (a,b+1)) delta2
  where
    halfN = div symN 2
    delta1 = [(-halfN)..halfN]
    delta2 = [(-halfN)..(halfN-1)]

snakeInsideOut :: Int -> ([(Int,Int)], [(Int,Int)])
snakeInsideOut k = partition inside (snake k)


verifiedAsymmetricPair :: (Int,Int) -> (Int,Int)
verifiedAsymmetricPair (a,b) = if a > b
  then (a,b) else error "verifiedAsymmetricPair"


cell :: (Ord j, IdentifyT1 i1 j) =>
    Gensym i1 -> [i1] -> [i1] -> (Int,Int) -> (i1, [Clause j])
cell gensym xs ys (a,b) = let
  prod = gensym (a * (symN + 1) + b)
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


cellBisect :: forall i1 i2 j . (Ord j, IdentifyT1 i1 j, IdentifyT2 i2 j) =>
    Gensym i1 -> i2 -> [i1] -> [i1] -> Int -> [Clause j]
cellBisect gensym1 cellT2 xs ys a = let
  (g, clauses) = cell gensym1 xs ys (a,a)
  in clauses ++ formulaToClauses (equivalentT12 g cellT2)


-- input is LSFD
productsInside :: (Ord i1, Ord i2) => Gensym i1 ->
    [i1] -> [i1] -> i2 -> [(Int,Int)] -> [Clause (T12 i1 (Positional i2))]
productsInside gensym xs ys diagonalId pairs = concatMap forPair pairs
  where
    addTwoCells (a,b) = Positional diagonalId (a+b)
    forPair pair = cellSumMirrors gensym (addTwoCells pair) xs ys pair


-- input is LSFD
productsInsideBisect :: (Ord i1, Ord i2) => Gensym i1 ->
    [i1] -> [i1] -> i2 -> [Int] -> [Clause (T12 i1 (Positional i2))]
productsInsideBisect gensym xs ys diagonalId as =
  concatMap forEntry as ++ holesAreZero
  where
    productBisect a = Positional diagonalId (2*a)
    hole a = Positional diagonalId (2*a-1)
    forEntry a = cellBisect gensym (productBisect a) xs ys a
    holesAreZero = concatMap (formulaToClauses . zeroT2 . hole) (tail as)


zeroOutside :: (Ord i1, Ord i2) =>
    i2 -> [(Int,Int)] -> [Clause (T12 i1 (Positional i2))]
zeroOutside diagonalId pairs = concatMap forPair pairs
  where
    forPair (a,b) = formulaToClauses $ zeroT2 (Positional diagonalId (a+b))

-- We need to collect all T1 labels in one type.
data CollectT1 a b = GensymId a | Number (Positional b)
  deriving (Eq, Ord, Read, Show)

getNumber :: CollectT1 a b -> Maybe (Positional b)
getNumber (Number p) = Just p
getNumber _ = Nothing

-- portmanteau to reduce the clutter
type Strint = (String, Int)

makeGensym :: Int -> String -> Int -> CollectT1 Strint a
makeGensym k c n = GensymId (c, k+n)

biDiagonal :: String -> Int -> [Positional Strint]
biDiagonal g k = makeNumber (g,k) (2 * symN + 1)

bisectional :: String -> [Positional Strint]
bisectional g = makeNumber (g,-1) (2 * symN + 1)


snakeClauses :: String -> [CollectT1 Strint String] -> [CollectT1 Strint String] ->
    Int -> [Clause (T12 (CollectT1 Strint String) (Positional Strint))]
snakeClauses g as bs k = validDiagonal ++
  zeroOutside (g,k) outside ++
  productsInside (makeGensym 0 g) as bs (g,k) inside
  where
    validDiagonal = concatMap (formulaToClauses . isValidT2) (biDiagonal g k)
    (inside, outside) = snakeInsideOut k


bisectClauses :: String -> [CollectT1 Strint String] -> [CollectT1 Strint String] ->
    [Clause (T12 (CollectT1 Strint String) (Positional Strint))]
bisectClauses g as bs = validDiagonal ++
  productsInsideBisect (makeGensym 0 g) as bs (g,-1) [0..symN]
  where
    validDiagonal = concatMap (formulaToClauses . isValidT2) (bisectional g)


-- large enough to avoid overlapping gensyms
offset = 1000

-- This is all very ad hoc at the moment.  Here the number of digits is currently
-- hardwired in the implementation: it only works for symN = 6.
-- We multiply two T1-represented numbers of 7 digits.
-- The result will be a T2-represented number of 15 digits.

multiplyNumbers :: String -> String -> String ->
    [CollectT1 Strint String] -> [CollectT1 Strint String] -> [Positional Strint] ->
    [Clause (T12 (CollectT1 Strint String) (Positional Strint))]
multiplyNumbers g gg ggg as bs cs = let
  c1 = makeNumber (ggg,1) (2 * symN + 2)
  c2 = makeNumber (ggg,2) (2 * symN + 2)
  in
  concat (map (snakeClauses g as bs) [0..(div symN 2 - 1)]) ++
  bisectClauses g as bs ++
  concatMap (formulaToClauses . isValidT2) (concat [c1,c2]) ++
  addNumbers (makeGensym offset     gg) (biDiagonal g 0) (biDiagonal g 1) c1 ++
  addNumbers (makeGensym (2*offset) gg) (biDiagonal g 2) (bisectional g)  c2 ++
  addNumbers (makeGensym (3*offset) gg) c1 c2 cs

verifiedInput :: Int -> Int -> Int
verifiedInput lenX lenY = if lenX == lenY && lenX == 2 * symN
  then lenX else error "verifiedInput"


-- integer factoring example
test = let
  as = map Number $ makeNumber "a" (symN + 1)
  bs = map Number $ makeNumber "b" (symN + 1)
  cs = makeNumber ("c",0) (2 * symN + 3)
  in
  concatMap (formulaToClauses . isValidT1) (concat [as,bs]) ++
  concatMap (formulaToClauses . isValidT2) (concat [cs]) ++
  multiplyNumbers "A" "B" "C" as bs cs ++
  integerEqualsNumberT2 (1089*1091) cs
