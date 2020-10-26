module Matrix where

import Data.List (transpose, (\\))

import Formula
import Clauses
import Digits
import Numbers
import AddNumbers
import MultiplyNumbers
import MultiplicationCommon

data Vector = Vector [Scalar]
  deriving (Eq, Ord, Read, Show)

identifierList :: Scalar -> [CollectT1 Strint String]
identifierList (Scalar _ i) = i

isNonZeroVector :: Vector -> ClauseList
isNonZeroVector (Vector xs) =
  let numbers = map identifierList xs
      allZero = conjunction (map isZeroT1 numbers)
  in formulaToClauses (Not allZero)


inner2 :: Label -> Vector -> Vector -> ([Positional Strint], ClauseList)
inner2 label
    (Vector [Scalar a as, Scalar b bs])
    (Vector [Scalar c cs, Scalar d ds]) =
  let
  ac = a ++ c
  bd = b ++ d
  xs = makeNumber (ac, 0) (2 * symN + 3)
  ys = makeNumber (bd, 0) (2 * symN + 3)
  zs = makeNumber (label, 0) (2 * symN + 4)
  clauses = concatMap (formulaToClauses . isValidT2) (concat [xs,ys,zs]) ++
      multiplyNumbers ('A':ac) ('B':ac) ('C':ac) as cs xs ++
      multiplyNumbers ('A':bd) ('B':bd) ('C':bd) bs ds ys ++
      addNumbers (makeGensym 0 ('H':label)) xs ys zs
  in (zs, clauses)


inner4 :: Label -> Vector -> Vector -> ([Positional Strint], ClauseList)
inner4 label (Vector [a1, b1, c1, d1]) (Vector [a2, b2, c2, d2]) =
  let
  (xs, clauses_x) = inner2 (label ++ "x") (Vector [a1, b1]) (Vector [a2, b2])
  (ys, clauses_y) = inner2 (label ++ "y") (Vector [c1, d1]) (Vector [c2, d2])
  zs = makeNumber (label, 0) (2 * symN + 5)
  in (zs,
      concatMap (formulaToClauses . isValidT2) zs ++
      clauses_x ++ clauses_y ++
      addNumbers (makeGensym 0 ('i':label)) xs ys zs)


data Matrix e = Matrix [[e]]
  deriving (Eq, Ord, Read, Show)

row :: Int -> Matrix Scalar -> Vector
row k (Matrix rows) = Vector (rows !! (k-1))

col :: Int -> Matrix Scalar -> Vector
col k (Matrix rows) = Vector (transpose rows !! (k-1))

matrixEntry :: Matrix Scalar -> Int -> Int -> Scalar
matrixEntry (Matrix rows) i j = (rows !! (i-1)) !! (j-1)

chunk4 :: [e] -> [[e]]
chunk4 [] = []
chunk4 (a:b:c:d:es) = [a,b,c,d] : chunk4 es

indices4 = [1,2,3,4]
indexPairs = [(i,j) | i <- indices4, j <- indices4]


matrixProduct4 :: Label -> Matrix Scalar -> Matrix Scalar ->
  (Matrix (Label, [Positional Strint]), ClauseList)
matrixProduct4 label x y = let
  inn (i,j) = let lab = label ++ show (i,j)
                  (zs, clauses) = inner4 lab (row i x) (col j y)
              in ((lab, zs), clauses)
  inners = map inn indexPairs
  in (Matrix (chunk4 $ map fst inners), concatMap snd inners)


-- Using this as a simple approximate expression of non-singularity
isWeaklyNonSingularMatrix :: Matrix Scalar -> ClauseList
isWeaklyNonSingularMatrix (Matrix rows) =
  concatMap (isNonZeroVector . Vector) (rows ++ transpose rows)


isIdentityMatrix :: Matrix Scalar -> ClauseList
isIdentityMatrix (Matrix rows) = let
  entries = concat rows
  ones = [0,5,10,15]
  zeros = [0..15] \\ ones
  entry i = entries !! i
  in
  concatMap (scalarIsZero . entry) zeros ++
  concatMap (scalarIsOne . entry) ones

makeLabel :: String -> Int -> String
makeLabel prefix i = prefix ++ show i

identityMatrix :: (Matrix Scalar, ClauseList)
identityMatrix = let
  (mat, clauses) = makeScalarMatrix "id"
  in (mat, clauses ++ isIdentityMatrix mat)

isNonNegativeMatrix :: Matrix Scalar -> ClauseList
isNonNegativeMatrix (Matrix rows) = concatMap isNonNegativeScalar (concat rows)

makeScalarMatrix :: String -> (Matrix Scalar, ClauseList)
makeScalarMatrix label = let
  makeRow i = unzip $ map (makeScalar . makeLabel (label ++ show i)) indices4
  rows = map makeRow indices4
  mat = Matrix (map fst rows)
  clauses = concat (concatMap snd rows)
  in (mat, clauses)

makeNonNegativeScalarMatrix :: String -> (Matrix Scalar, ClauseList)
makeNonNegativeScalarMatrix label = let
  (mat, clauses) = makeScalarMatrix label
  in (mat, clauses ++ isNonNegativeMatrix mat)


-- this is very ad hoc for now
difference :: Label ->
    ((Label, [Positional Strint]),
     (Label, [Positional Strint])) ->
    ([Positional Strint], ClauseList)
difference label ((lab_a, as), (lab_b, bs)) = let
  lab = label ++ lab_a ++ lab_b
  xs = makeNumber ('d':lab, 0) (2 * symN + 6)
  clauses = concatMap (formulaToClauses . isValidT2) xs ++
            subtractNumbers (makeGensym 0 ('s':lab)) as bs xs
  in (xs, clauses)


matrixGreaterThan :: Label ->
    Matrix (Label, [Positional Strint]) ->
    Matrix (Label, [Positional Strint]) -> ClauseList
matrixGreaterThan label (Matrix rows_a) (Matrix rows_b) = let
  entries_a = concat rows_a
  entries_b = concat rows_b
  (diffs, diff_clauses) = unzip $ map (difference label) $ zip entries_a entries_b
  in
  concat diff_clauses ++
  concatMap isNonNegativeT2 diffs ++
  formulaToClauses (disjunction $ map nonZeroNumberT2 diffs)


sameNumberT12 :: Scalar -> (Label, [Positional Strint]) -> ClauseList
sameNumberT12 (Scalar _ as) (_, bs) = formulaToClauses $
  equivalentNumbersT12 as bs

sameMatrixT12 :: Matrix Scalar -> Matrix (Label, [Positional Strint]) -> ClauseList
sameMatrixT12 (Matrix rows_1) (Matrix rows_2) = concat $
  zipWith sameNumberT12 (concat rows_1) (concat rows_2)

productGreaterThanProduct :: Label ->
    (Matrix Scalar, Matrix Scalar) ->
    (Matrix Scalar, Matrix Scalar) -> ClauseList
productGreaterThanProduct label (a,b) (c,d) = let
  (ab, clauses_ab) = matrixProduct4 ("ab" ++ label) a b
  (cd, clauses_cd) = matrixProduct4 ("cd" ++ label) c d
  in
  clauses_ab ++ clauses_cd ++
  matrixGreaterThan ("GT" ++ label) ab cd


test :: ClauseList
test = let
  (a,clauses_a) = makeNonNegativeScalarMatrix "a"
  (b,clauses_b) = makeNonNegativeScalarMatrix "b"
  in clauses_a ++ clauses_b ++
     productGreaterThanProduct "test" (a,b) (b,a)
