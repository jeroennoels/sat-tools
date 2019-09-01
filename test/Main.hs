module Main (main) where

import Tools
import Formula
import Eval
import Arbitraries

import Test.QuickCheck
import Control.Monad (liftM, liftM2)

example1 :: Formula Int
example1 = (Not (Var 1) `Or` Var 2) `Equiv` (Var 1 `Implies` Var 2)

example2 :: IO (Formula IntLabel)
example2 = generate arbitrary

tautology :: Ord i => Formula i -> Bool
tautology f = all (evaluate f) (allAssignments $ variables f)

main :: IO ()
main = sequence_ $ map putStrLn result
