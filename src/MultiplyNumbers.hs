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


data Quux a b = GensymId a | Number (Positional b)
  deriving (Eq, Ord, Read, Show)

getNumber :: Quux a b -> Maybe (Positional b)
getNumber (Number p) = Just p
getNumber _ = Nothing

type Chint = (String, Int)

makeGensym :: Int -> String -> Int -> Quux Chint a
makeGensym k c n = GensymId (c, k+n)

biDiagonal :: String -> Int -> [Positional Chint]
biDiagonal g k = makeNumber (g,k) (2 * symN + 1)

bisectional :: String -> [Positional Chint]
bisectional g = makeNumber (g,-1) (2 * symN + 1)


snakeClauses :: String -> [Quux Chint String] -> [Quux Chint String] ->
    Int -> [Clause (T12 (Quux Chint String) (Positional Chint))]
snakeClauses g as bs k = validDiagonal ++
  zeroOutside (g,k) outside ++
  productsInside (makeGensym 0 g) as bs (g,k) inside
  where
    validDiagonal = concatMap (formulaToClauses . isValidT2) (biDiagonal g k)
    (inside, outside) = snakeInsideOut k


bisectClauses :: String -> [Quux Chint String] -> [Quux Chint String] ->
    [Clause (T12 (Quux Chint String) (Positional Chint))]
bisectClauses g as bs = validDiagonal ++
  productsInsideBisect (makeGensym 0 g) as bs (g,-1) [0..symN]
  where
    validDiagonal = concatMap (formulaToClauses . isValidT2) (bisectional g)

  
-- large enough to avoid overlapping gensyms 
offset = 1000

multiplyNumbers :: String -> String -> String ->
    [Quux Chint String] -> [Quux Chint String] -> [Positional Chint] ->
    [Clause (T12 (Quux Chint String) (Positional Chint))]
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


test_factoring = let
  as = map Number $ makeNumber "a" (symN + 1)
  bs = map Number $ makeNumber "b" (symN + 1)
  cs = makeNumber ("c",0) (2 * symN + 3)
  in
  concatMap (formulaToClauses . isValidT1) (concat [as,bs]) ++
  concatMap (formulaToClauses . isValidT2) (concat [cs]) ++
  multiplyNumbers "A" "B" "C" as bs cs ++
  integerEqualsNumberT2 (1089*1091) cs

type Label = String

type ClauseList = [Clause (T12 (Quux Chint Label) (Positional Chint))]
  
data Scalar = Scalar Label [Quux Chint String]
  deriving (Eq, Ord, Read, Show)

makeScalar :: Label -> (Scalar, ClauseList)
makeScalar label = (Scalar label as, clauses)
  where
    as = map Number $ makeNumber label (symN + 1)
    clauses = concatMap (formulaToClauses . isValidT1) as

data Vector = Vector Scalar Scalar
  deriving (Eq, Ord, Read, Show)

inner :: Label -> Vector -> Vector -> ([Positional Chint], ClauseList) 
inner label (Vector (Scalar a as) (Scalar b bs)) (Vector (Scalar c cs) (Scalar d ds)) = let
  ac = a ++ c
  bd = b ++ d
  xs = makeNumber (ac, 0) (2 * symN + 3)
  ys = makeNumber (bd, 0) (2 * symN + 3)
  zs = makeNumber (label, 0) (2 * symN + 4)
  clauses = concatMap (formulaToClauses . isValidT2) (concat [xs,ys,zs]) ++
      multiplyNumbers ('A':ac) ('B':ac) ('C':ac) as cs xs ++
      multiplyNumbers ('A':bd) ('B':bd) ('C':bd) bs ds ys ++
      addNumbers (makeGensym 0 ('G':label)) xs ys zs 
  in (zs, clauses)


data Matrix e = Matrix e e e e 
  deriving (Eq, Ord, Read, Show)

row :: Int -> Matrix Scalar -> Vector
row 1 (Matrix a b _ _) = Vector a b
row 2 (Matrix _ _ c d) = Vector c d

col :: Int -> Matrix Scalar -> Vector
col 1 (Matrix a _ c _) = Vector a c
col 2 (Matrix _ b _ d) = Vector b d

matrixProduct :: Label -> Matrix Scalar -> Matrix Scalar ->
  (Matrix (Label, [Positional Chint]), ClauseList)
matrixProduct label x y = let
  label_11 = label ++ "-11"
  label_12 = label ++ "-12"
  label_21 = label ++ "-21"
  label_22 = label ++ "-22"
  (zs_11, clauses_11) = inner label_11 (row 1 x) (col 1 y)
  (zs_12, clauses_12) = inner label_12 (row 1 x) (col 2 y)
  (zs_21, clauses_21) = inner label_21 (row 2 x) (col 1 y)
  (zs_22, clauses_22) = inner label_22 (row 2 x) (col 2 y)
  in
  (Matrix (label_11, zs_11) (label_12, zs_12) (label_21, zs_21) (label_22, zs_22),
   clauses_11 ++ clauses_12 ++ clauses_21 ++ clauses_22)


matrixEqual :: Matrix (Label, [Positional Chint]) -> Matrix Integer -> ClauseList
matrixEqual (Matrix (_,as) (_,bs) (_,cs) (_,ds)) (Matrix a b c d) = let
  zero = makeNumber ("zero", 0) (2 * symN + 5)
  nas = makeNumber ("nas", 0) (2 * symN + 4)
  nbs = makeNumber ("nbs", 0) (2 * symN + 4)
  ncs = makeNumber ("ncs", 0) (2 * symN + 4)
  nds = makeNumber ("nds", 0) (2 * symN + 4)
  in
  concatMap (formulaToClauses . isValidT2) (concat [zero,nas,nbs,ncs,nds]) ++
  addNumbers (makeGensym 0 ("Ha")) as nas zero ++
  addNumbers (makeGensym 0 ("Hb")) bs nbs zero ++
  addNumbers (makeGensym 0 ("Hc")) cs ncs zero ++
  addNumbers (makeGensym 0 ("Hd")) ds nds zero ++
  integerEqualsNumberT2 0 zero ++
  integerEqualsNumberT2 (-a) nas ++
  integerEqualsNumberT2 (-b) nbs ++ 
  integerEqualsNumberT2 (-c) ncs ++
  integerEqualsNumberT2 (-d) nds

             
test :: ClauseList
test = let
  [a,b,c,d] = map makeScalar ["a", "b", "c", "d"]
  x = Matrix (fst a) (fst b) (fst c) (fst d)
  (xx, clauses) = matrixProduct "mat" x x
  in 
  snd a ++ snd b ++ snd c ++ snd d ++ clauses ++
  matrixEqual xx (Matrix 20000 20000 20000 20000)
