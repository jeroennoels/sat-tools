module Main (main) where

import Formula
import Eval
import Arbitraries
import Clauses
import Dimacs
import Digits
import AddT1
import AddT2
import AddNumbers
import MultiplyT1
import Tools

import TestAddT1
import TestAddT2
import TestAddNumbers
import TestMultiplyT1

import System.Environment (getArgs)
import Test.QuickCheck
import Control.Arrow ((&&&))
import Control.Applicative (liftA2)
import Data.Set (Set)
import qualified Data.Set as Set

example1 :: Formula Int
example1 = (Not (Var 1) `Or` Var 2) `Equiv` (Var 1 `Implies` Var 2)

example2 :: Formula Int
example2 = ((Not (Var 1) `And` Var 4) `Equiv` (Var 2 `Or` Var 1)) `Or` Var 3

example3 :: IO (Formula IntLabel)
example3 = generate (arbitrarySizedFormula 100)

tautology :: Ord i => Formula i -> Bool
tautology f = all (evaluate f) (allAssignments $ variables f)

(<-->) :: Ord i => Formula i -> Formula i -> Bool
(<-->) f g = all (equalOn f g) (allAssignments vars)
  where vars = variables f `Set.union` variables g

(<==>) :: Ord i => [Clause i] -> Formula i -> Bool
(<==>) cs f = all (equivalentOn cs f) (allAssignments $ variables f)

prop_elimImplication :: Formula IntLabel -> Bool
prop_elimImplication f = elimImplication f <--> f

prop_moveNotDown :: Formula IntLabel -> Bool
prop_moveNotDown f = moveNotDown (elimImplication f) <--> f

-- Slow because it deals with CNF before it is simplified.
prop_toCNF :: Formula IntLabel -> Bool
prop_toCNF f = toCNF f <--> f

prop_Clauses :: Formula IntLabel -> Bool
prop_Clauses f = formulaToClauses f <==> f

assert :: String -> Bool -> IO ()
assert msg ok = putStrLn $ msg ++ if ok then " -> OK" else error msg

runTests :: IO ()
runTests = sequence_ $
  [assert "testMultiply" testMultiply,
   assert "testAddDigitsT1" testAddDigitsT1,
   assert "testAddDigitsT2" testAddDigitsT2
  ] ++
  map quickCheck [prop_elimImplication,
                  prop_moveNotDown,
                  prop_Clauses]

main :: IO ()
main = getArgs >>= run

readLinesFromFile :: FilePath -> IO [String]
readLinesFromFile file = lines `fmap` readFile file  

loadMapping :: IO [(Int, T12 Char Char)]
loadMapping = readMapping `fmap` readLinesFromFile "problem.cnf" 

loadVariables :: IO [Int]
loadVariables = readVariables `fmap` readLinesFromFile "out.dimacs"
    
run :: [String] -> IO ()
run ["t"] = runTests
run ["t2"] = sequence_ $ map print $ zip testAddNumbers [1..]
run ["p"] = dimacsOutput $ addABXY
run ["i"] = loadMapping >>= print
run ["s"] = loadVariables >>= print
run ["m"] = liftA2 combine loadVariables loadMapping >>= print 
  where combine results mapping = interpretation (getModel results mapping)
