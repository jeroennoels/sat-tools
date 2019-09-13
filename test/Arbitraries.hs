module Arbitraries where

import Formula

import Test.QuickCheck
import Control.Monad (liftM, liftM2)


instance Arbitrary i => Arbitrary (Formula i) where
  arbitrary = sized arbitrarySizedFormula

arbitrarySizedFormula :: Arbitrary i => Int -> Gen (Formula i)
arbitrarySizedFormula 0 = liftM Var arbitrary
arbitrarySizedFormula n = oneof [
    liftM Var arbitrary,
    liftM Not big,
    liftM2 Or sub sub,
    liftM2 And big big,
    liftM2 Implies sub sub,
    liftM2 Equiv sub sub]
  where
    sub = arbitrarySizedFormula (div (2*n) 7)
    big = arbitrarySizedFormula (div (2*n) 3)


instance Arbitrary IntLabel where
  arbitrary = liftM IntLabel $ choose (1,9)
