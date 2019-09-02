module Main (main) where

import Tools
import Formula
import Eval
import Arbitraries

import Test.QuickCheck
import Control.Arrow ((&&&))
import Data.Set (Set)
import qualified Data.Set as Set

example1 :: Formula Int
example1 = (Not (Var 1) `Or` Var 2) `Equiv` (Var 1 `Implies` Var 2)

example2 :: Formula Int
example2 = Not (Var 1) `Or` Var 2

example3 :: IO (Formula IntLabel)
example3 = generate arbitrary

tautology :: Ord i => Formula i -> Bool
tautology f = all (evaluate f) (allAssignments $ variables f)

(<-->) :: Ord i => Formula i -> Formula i -> Bool
(<-->) f g = all (equalOn f g) (allAssignments vars)
  where vars = variables f `Set.union` variables g

prop_elimImplication :: Formula IntLabel -> Bool
prop_elimImplication f = elimImplication f <--> f

runTests :: IO ()
runTests = quickCheck prop_elimImplication

main :: IO ()
main = sequence_ $ map putStrLn result
