{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module MatrixTwoByTwo where

import Formula
import Clauses
import Digits
import Numbers
import AddNumbers
import MultiplyNumbers
import MultiplicationCommon


-- For a first experiment we just hardcode types for 2 x 2 matrices.
data Vector = Vector Scalar Scalar
  deriving (Eq, Ord, Read, Show)

inner :: Label -> Vector -> Vector -> ([Positional Strint], ClauseList)
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

-- For a first experiment we just hardcode types for 2 x 2 matrices.

data Matrix e = Matrix e e e e
  deriving (Eq, Ord, Read, Show)

row :: Int -> Matrix Scalar -> Vector
row 1 (Matrix a b _ _) = Vector a b
row 2 (Matrix _ _ c d) = Vector c d

col :: Int -> Matrix Scalar -> Vector
col 1 (Matrix a _ c _) = Vector a c
col 2 (Matrix _ b _ d) = Vector b d


matrixProduct :: Label -> Matrix Scalar -> Matrix Scalar ->
  (Matrix (Label, [Positional Strint]), ClauseList)
matrixProduct label x y = let
  lab_11 = label ++ "-11"
  lab_12 = label ++ "-12"
  lab_21 = label ++ "-21"
  lab_22 = label ++ "-22"
  (zs_11, clauses_11) = inner lab_11 (row 1 x) (col 1 y)
  (zs_12, clauses_12) = inner lab_12 (row 1 x) (col 2 y)
  (zs_21, clauses_21) = inner lab_21 (row 2 x) (col 1 y)
  (zs_22, clauses_22) = inner lab_22 (row 2 x) (col 2 y)
  in
  (Matrix (lab_11, zs_11) (lab_12, zs_12) (lab_21, zs_21) (lab_22, zs_22),
   clauses_11 ++ clauses_12 ++ clauses_21 ++ clauses_22)


matrixEqual :: Label -> Matrix (Label, [Positional Strint]) -> Matrix Integer -> ClauseList
matrixEqual label
    (Matrix (lab_a, as) (lab_b, bs) (lab_c, cs) (lab_d, ds))
    (Matrix a b c d) =
  let
  ll_a = label ++ lab_a
  ll_b = label ++ lab_b
  ll_c = label ++ lab_c
  ll_d = label ++ lab_d
  aa = makeNumber ('g':ll_a, 0) (2 * symN + 4)
  bb = makeNumber ('g':ll_b, 0) (2 * symN + 4)
  cc = makeNumber ('g':ll_c, 0) (2 * symN + 4)
  dd = makeNumber ('g':ll_d, 0) (2 * symN + 4)
  in
  concatMap (formulaToClauses . isValidT2) (concat [aa,bb,cc,dd]) ++
  subtractNumbers (makeGensym 0 ('G':ll_a)) as aa (fst zero) ++
  subtractNumbers (makeGensym 0 ('G':ll_b)) bs bb (fst zero) ++
  subtractNumbers (makeGensym 0 ('G':ll_c)) cs cc (fst zero) ++
  subtractNumbers (makeGensym 0 ('G':ll_d)) ds dd (fst zero) ++
  integerEqualsNumberT2 a aa ++
  integerEqualsNumberT2 b bb ++
  integerEqualsNumberT2 c cc ++
  integerEqualsNumberT2 d dd

isPositiveMatrix :: Matrix Scalar -> ClauseList
isPositiveMatrix (Matrix a b c d) = concatMap isPositiveScalar [a,b,c,d]

isNonNegativeMatrix :: Matrix Scalar -> ClauseList
isNonNegativeMatrix (Matrix a b c d) = concatMap isNonNegativeScalar [a,b,c,d]

matrixGreaterThan :: Label ->
    Matrix (Label, [Positional Strint]) ->
    Matrix (Label, [Positional Strint]) -> ClauseList
matrixGreaterThan label
    (Matrix (lab_xa, xas) (lab_xb, xbs) (lab_xc, xcs) (lab_xd, xds))
    (Matrix (lab_ya, yas) (lab_yb, ybs) (lab_yc, ycs) (lab_yd, yds)) =
  let
  ll_a = label ++ lab_xa ++ lab_ya
  ll_b = label ++ lab_xb ++ lab_yb
  ll_c = label ++ lab_xc ++ lab_yc
  ll_d = label ++ lab_xd ++ lab_yd
  aa = makeNumber ('g':ll_a, 0) (2 * symN + 5)
  bb = makeNumber ('g':ll_b, 0) (2 * symN + 5)
  cc = makeNumber ('g':ll_c, 0) (2 * symN + 5)
  dd = makeNumber ('g':ll_d, 0) (2 * symN + 5)
  in
  concatMap (formulaToClauses . isValidT2) (concat [aa,bb,cc,dd]) ++
  subtractNumbers (makeGensym 0 ('G':ll_a)) xas yas aa ++
  subtractNumbers (makeGensym 0 ('G':ll_b)) xbs ybs bb ++
  subtractNumbers (makeGensym 0 ('G':ll_c)) xcs ycs cc ++
  subtractNumbers (makeGensym 0 ('G':ll_d)) xds yds dd ++
  concatMap isNonNegativeT2 [aa,bb,cc,dd] ++
  formulaToClauses (nonZeroNumberT2 aa `Or` nonZeroNumberT2 bb `Or`
                    nonZeroNumberT2 cc `Or` nonZeroNumberT2 dd)

-- Factoring a 2 x 2 matrix.  Takes about 1 minute with Cadical.
test_factor_matrix :: ClauseList
test_factor_matrix = let
  [xa,xb,xc,xd] = map makeScalar ["xa", "xb", "xc", "xd"]
  [ya,yb,yc,yd] = map makeScalar ["ya", "yb", "yc", "yd"]
  x = Matrix (fst xa) (fst xb) (fst xc) (fst xd)
  y = Matrix (fst ya) (fst yb) (fst yc) (fst yd)
  (xy, clauses) = matrixProduct "mat" x y
  in
  isPositiveMatrix x ++  isPositiveMatrix y ++
  snd zero ++
  concatMap snd [xa,xb,xc,xd] ++
  concatMap snd [ya,yb,yc,yd] ++
  clauses ++
  matrixEqual "ME" xy (Matrix 44953 29609 47407 40127)


makeNonNegativeScalarMatrix :: String -> (Matrix Scalar, ClauseList)
makeNonNegativeScalarMatrix label = let
  [a,b,c,d] = map (makeScalar . (label ++)) ["a","b","c","d"]
  mat = Matrix (fst a) (fst b) (fst c) (fst d)
  clauses = concatMap snd [a,b,c,d] ++ isNonNegativeMatrix mat
  in (mat, clauses)

test_commutator :: ClauseList
test_commutator = let
  (x, clauses_x) = makeNonNegativeScalarMatrix "x"
  (y, clauses_y) = makeNonNegativeScalarMatrix "y"
  (xy, clauses_xy) = matrixProduct "xy" x y
  (yx, clauses_yx) = matrixProduct "yx" y x
  in
  clauses_x ++ clauses_y ++ clauses_xy ++ clauses_yx ++
  matrixGreaterThan "GT" xy yx


productGreaterThanProduct :: Label ->
    (Matrix Scalar, Matrix Scalar) ->
    (Matrix Scalar, Matrix Scalar) -> ClauseList
productGreaterThanProduct label (a,b) (c,d) = let
  (ab, clauses_ab) = matrixProduct "ab" a b
  (cd, clauses_cd) = matrixProduct "cd" c d
  in
  clauses_ab ++ clauses_cd ++
  matrixGreaterThan ("GT" ++ label) ab cd

isIdentityMatrix :: Matrix Scalar -> ClauseList
isIdentityMatrix (Matrix a b c d) =
  concatMap scalarIsZero [b,c] ++ concatMap scalarIsOne [a,d]

identityMatrix :: (Matrix Scalar, ClauseList)
identityMatrix = let
  [a,b,c,d] = map makeScalar ["ia","ib","ic","id"]
  mat = Matrix (fst a) (fst b) (fst c) (fst d)
  clauses = concatMap snd [a,b,c,d] ++ isIdentityMatrix mat
  in (mat, clauses)
