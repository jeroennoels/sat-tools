{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Main (main) where

import Tools
import Formula
import Eval
import Assignment

import Test.QuickCheck
import Control.Monad (liftM, liftM2)

example1 :: Formula Int
example1 = (Not (Var 1) `Or` Var 2) `Equiv` (Var 1 `Implies` Var 2)

example2 :: IO (Formula IntLabel)
example2 = generate arbitrary

instance Arbitrary i => Arbitrary (Formula i) where
  arbitrary = sized arbitrarySizedFormula

arbitrarySizedFormula :: Arbitrary i => Int -> Gen (Formula i)
arbitrarySizedFormula 0 = liftM Var arbitrary
arbitrarySizedFormula n = oneof [
    liftM Var arbitrary,
    liftM Not sub,
    liftM2 Or sub sub,
    liftM2 And sub sub,
    liftM2 Implies sub sub,
    liftM2 Equiv sub sub]
  where sub = arbitrarySizedFormula (div (2*n) 3)


newtype IntLabel = IntLabel Int deriving (Eq, Ord)

instance Show IntLabel where
  show (IntLabel n) = show n
 
instance Arbitrary IntLabel where
  arbitrary = liftM IntLabel $ choose (1,9)

tautology :: Ord i => Formula i -> Bool
tautology f = all (evaluate f) (allAssignments $ variables f)

main :: IO ()
main = sequence_ $ map putStrLn result
