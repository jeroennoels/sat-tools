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

-- must be even
symN :: Int
symN = 14

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


data Quux a b = GensymId a | Number (Positional b)
  deriving (Eq, Ord, Read, Show)

getNumber :: Quux a b -> Maybe (Positional b)
getNumber (Number p) = Just p
getNumber _ = Nothing

type Chint = (Char, Int)

makeGensym :: Int -> Char -> Int -> Quux Chint a
makeGensym k c n = GensymId (c, k+n)

biDiagonal :: Char -> Int -> [Positional Chint]
biDiagonal g k = makeNumber (g,k) (2 * symN + 1)

bisectional :: Char -> [Positional Chint]
bisectional g = makeNumber (g,-1) (2 * symN + 1)


snakeClauses :: Char -> [Quux Chint Char] -> [Quux Chint Char] ->
    Int -> [Clause (T12 (Quux Chint Char) (Positional Chint))]
snakeClauses g as bs k = validDiagonal ++
  zeroOutside (g,k) outside ++
  productsInside (makeGensym 0 'P') as bs (g,k) inside
  where
    validDiagonal = concatMap (formulaToClauses . isValidT2) (biDiagonal g k)
    (inside, outside) = snakeInsideOut k


bisectClauses :: Char -> [Quux Chint Char] -> [Quux Chint Char] ->
    [Clause (T12 (Quux Chint Char) (Positional Chint))]
bisectClauses g as bs = validDiagonal ++
  productsInsideBisect (makeGensym 0 'P') as bs (g,-1) [0..symN]
  where
    validDiagonal = concatMap (formulaToClauses . isValidT2) (bisectional g)

t1 = map Number $ makeNumber 't' (2 * symN + 4) -- equal length for t1 and t2 
t2 = makeNumber ('t',2) (2 * symN + 4)

z0 = makeNumber ('z',0) (2 * symN + 5)

as' = map Number $ makeNumber 'a' (symN + 1)
bs' = map Number $ makeNumber 'b' (symN + 1)
cs' = makeNumber ('c',0) (2 * symN + 4)

test = multiplyNumbers 'q' 'G' as' as' cs' ++
  concatMap (formulaToClauses . isValidT1) (concat [as',as',t1]) ++
  concatMap (formulaToClauses . isValidT2) (concat [cs',t2,z0]) ++
  addNumbers (makeGensym 0 'T') cs' t2 z0 ++
  formulaToClauses (equivalentNumbersT12 t1 t2) ++
  integerEqualsNumberT1 (-2000000^2) t1 ++ 
  integerEqualsNumberT2 0 z0

-- large enough to avoid overlapping gensyms 
offset = 1000

multiplyNumbers :: Char -> Char ->
    [Quux Chint Char] -> [Quux Chint Char] -> [Positional Chint] ->
    [Clause (T12 (Quux Chint Char) (Positional Chint))]
multiplyNumbers g gg as bs cs = let
  c1 = makeNumber (g,1) (2 * symN + 2)
  c2 = makeNumber (g,2) (2 * symN + 2)
  c3 = makeNumber (g,3) (2 * symN + 2)
  c4 = makeNumber (g,4) (2 * symN + 2)
  u1 = makeNumber (g,5) (2 * symN + 3)
  u2 = makeNumber (g,6) (2 * symN + 3)
  d = 'D'
  in
  concat (map (snakeClauses d as bs) [0..(div symN 2 - 1)]) ++
  bisectClauses d as bs ++
  concatMap (formulaToClauses . isValidT2) (concat [c1,c2,c3,c4,u1,u2]) ++
  addNumbers (makeGensym offset     gg) (biDiagonal d 0) (biDiagonal d 1) c1 ++
  addNumbers (makeGensym (2*offset) gg) (biDiagonal d 2) (biDiagonal d 3) c2 ++
  addNumbers (makeGensym (3*offset) gg) (biDiagonal d 4) (biDiagonal d 5) c3 ++
  addNumbers (makeGensym (4*offset) gg) (biDiagonal d 6) (bisectional d)  c4 ++
  addNumbers (makeGensym (5*offset) gg) c1 c2 u1 ++
  addNumbers (makeGensym (6*offset) gg) c3 c4 u2 ++
  addNumbers (makeGensym (7*offset) gg) u1 u2 cs


verifiedInput :: Int -> Int -> Int
verifiedInput lenX lenY = if lenX == lenY && lenX == 2 * symN
  then lenX else error "verifiedInput"
