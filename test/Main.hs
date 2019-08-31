module Main (main) where

import Tools
import Formula
import Test.QuickCheck
import Control.Monad (liftM, liftM2)

example1 :: Formula Int
example1 = Var 1 `Or` Var 2

example2 :: IO (Formula IntLabel)
example2 = generate arbitrary

instance Arbitrary i => Arbitrary (Formula i) where
  arbitrary = sized arbitrarySizedFormula

arbitrarySizedFormula :: Arbitrary i => Int -> Gen (Formula i)
arbitrarySizedFormula 0 = liftM Var arbitrary
arbitrarySizedFormula n = oneof [arbitrarySizedFormula 0,
    liftM2 Or sub sub]
  where sub = arbitrarySizedFormula (div n 2)


newtype IntLabel = IntLabel Int

instance Show IntLabel where
  show (IntLabel n) = show n

instance Arbitrary IntLabel where
  arbitrary = liftM (IntLabel . getPositive) arbitrary

main :: IO ()
main = sequence_ $ map putStrLn result
