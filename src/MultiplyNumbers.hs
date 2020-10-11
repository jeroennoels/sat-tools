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
  productsInside (makeGensym 0 g) as bs (g,k) inside
  where
    validDiagonal = concatMap (formulaToClauses . isValidT2) (biDiagonal g k)
    (inside, outside) = snakeInsideOut k


bisectClauses :: Char -> [Quux Chint Char] -> [Quux Chint Char] ->
    [Clause (T12 (Quux Chint Char) (Positional Chint))]
bisectClauses g as bs = validDiagonal ++
  productsInsideBisect (makeGensym 0 g) as bs (g,-1) [0..symN]
  where
    validDiagonal = concatMap (formulaToClauses . isValidT2) (bisectional g)

as' = map Number $ makeNumber 'a' (symN + 1)
aas = makeNumber ('x',0) (2 * symN + 4)
bs' = map Number $ makeNumber 'b' (symN + 1)
bbs = makeNumber ('y',0) (2 * symN + 4)
cs' = map Number $ makeNumber 'c' (symN + 1)
ccs = makeNumber ('z',0) (2 * symN + 4)

ds' = map Number $ makeNumber 'd' (symN + 1)
dds = makeNumber ('u',0) (2 * symN + 5)
es' = map Number $ makeNumber 'e' (symN + 1)
ees = makeNumber ('v',0) (2 * symN + 5)
fs' = map Number $ makeNumber 'f' (symN + 1)
ffs = makeNumber ('w',0) (2 * symN + 5)

 
test =
  concatMap (formulaToClauses . isValidT1) (concat [as',bs',cs',ds',es',fs']) ++
  concatMap (formulaToClauses . isValidT2) (concat [aas,bbs,ccs,dds,ees,ffs]) ++
  nonZeroNumberT1 as' ++
  nonZeroNumberT1 bs' ++
  nonZeroNumberT1 cs' ++
  formulaToClauses (zeroT2 (last dds)) ++
  formulaToClauses (zeroT2 (last ees)) ++
  formulaToClauses (zeroT2 (last ffs)) ++
  multiplyNumbers 'D' 'K' 'k' as' as' aas ++
  multiplyNumbers 'E' 'L' 'l' bs' bs' bbs ++
  multiplyNumbers 'F' 'M' 'm' cs' cs' ccs ++
  multiplyNumbers 'G' 'N' 'n' ds' ds' (init dds) ++
  multiplyNumbers 'H' 'O' 'o' es' es' (init ees) ++
  multiplyNumbers 'I' 'P' 'p' fs' fs' (init ffs) ++
  addNumbers (makeGensym 0 'R') aas bbs dds ++
  addNumbers (makeGensym 0 'S') aas ccs ees ++
  addNumbers (makeGensym 0 'T') bbs ccs ffs

-- large enough to avoid overlapping gensyms 
offset = 1000

multiplyNumbers :: Char -> Char -> Char ->
    [Quux Chint Char] -> [Quux Chint Char] -> [Positional Chint] ->
    [Clause (T12 (Quux Chint Char) (Positional Chint))]
multiplyNumbers g gg ggg as bs cs = let
  c1 = makeNumber (ggg,1) (2 * symN + 2)
  c2 = makeNumber (ggg,2) (2 * symN + 2)
  c3 = makeNumber (ggg,3) (2 * symN + 2)
  c4 = makeNumber (ggg,4) (2 * symN + 2)
  u1 = makeNumber (ggg,5) (2 * symN + 3)
  u2 = makeNumber (ggg,6) (2 * symN + 3)
  in
  concat (map (snakeClauses g as bs) [0..(div symN 2 - 1)]) ++
  bisectClauses g as bs ++
  concatMap (formulaToClauses . isValidT2) (concat [c1,c2,c3,c4,u1,u2]) ++
  addNumbers (makeGensym offset     gg) (biDiagonal g 0) (biDiagonal g 1) c1 ++
  addNumbers (makeGensym (2*offset) gg) (biDiagonal g 2) (biDiagonal g 3) c2 ++
  addNumbers (makeGensym (3*offset) gg) (biDiagonal g 4) (biDiagonal g 5) c3 ++
  addNumbers (makeGensym (4*offset) gg) (biDiagonal g 6) (bisectional g)  c4 ++
  addNumbers (makeGensym (5*offset) gg) c1 c2 u1 ++
  addNumbers (makeGensym (6*offset) gg) c3 c4 u2 ++
  addNumbers (makeGensym (7*offset) gg) u1 u2 cs


verifiedInput :: Int -> Int -> Int
verifiedInput lenX lenY = if lenX == lenY && lenX == 2 * symN
  then lenX else error "verifiedInput"
