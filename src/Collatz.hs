module Collatz where

import Formula
import Clauses
import Digits
import Numbers
import AddNumbers
import MultiplyNumbers
import MultiplicationCommon
import Matrix

-- See "Encoding Challenges for Hard Problems" by Marijn J.H. Heule:
-- https://matryoshka-project.github.io/matryoshka2019/slides/heule-encoding-challenges.pdf

test :: ClauseList
test = let
  (i, identity) = identityMatrix
  matrices = map makeNonNegativeScalarMatrix ["f","p","q","r","t","c","d"]
  ([f,p,q,r,t,c,d], clausesList) = unzip matrices
  in
  identity ++ concat clausesList ++
  concatMap isWeaklyNonSingularMatrix [f,p,q,r,t,c,d] ++
  productGreaterThanProduct "F1" (f,p) (p,f) ++
  productGreaterThanProduct "F2" (f,q) (p,t) ++
  productGreaterThanProduct "F3" (f,r) (q,f) ++
  productGreaterThanProduct "T1" (t,p) (q,t) ++
  productGreaterThanProduct "T2" (t,q) (r,f) ++
  productGreaterThanProduct "T3" (t,r) (r,t) ++
  productGreaterThanProduct "D1" (f,d) (i,d) ++
  productGreaterThanProduct "D2" (t,d) (r,d) ++
  productGreaterThanProduct "C1" (c,p) (c,t) ++
  productGreaterThanProduct "C2" (i,q) (f,f) ++
  productGreaterThanProduct "C3" (i,r) (f,t)
