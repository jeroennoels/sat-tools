{-# LANGUAGE ScopedTypeVariables #-}
module Dimacs where

import Clauses

import Data.Tuple (swap)
import Data.Maybe (fromJust, mapMaybe)
import Data.List (intercalate, isPrefixOf)
import Data.Map.Strict (Map, (!))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

-- Enumerate all distinct variables in a given collection of clauses.
-- Then map variable identifiers to positive integers, based on their
-- position in that enumeration.
enumerateVariables :: Ord i => [Clause i] -> Map i Int
enumerateVariables clauses = Map.fromList (zip vars [1..])
  where vars = Set.toAscList (distinctVariables clauses)

clauseToDimacs :: forall i . Ord i => Map i Int -> Clause i -> String
clauseToDimacs enumeration (Clause literals) = intercalate " " shows ++ " 0"
  where
    shows :: [String]
    shows = map (show . toInt) literals
    toInt :: Literal i -> Int
    toInt (Positive var) = enumeration ! var
    toInt (Negative var) = negate (enumeration ! var)

toDimacsLines :: (Show i, Ord i) => [Clause i] -> [String]
toDimacsLines clauses = mapping ++ problem : map (clauseToDimacs enum) clauses
  where enum = enumerateVariables clauses
        mapping = map (("c " ++) . show) (Map.toAscList enum)
        problem = "p cnf " ++ show (length enum) ++ " " ++ show (length clauses)

dimacsOutput :: (Show i, Ord i) => [Clause i] -> IO ()
dimacsOutput = sequence_ . map putStrLn . toDimacsLines

readMapping :: Read i => [String] -> [(Int, i)]
readMapping = map (swap . read . drop 2) . filter (isPrefixOf "c ")

readInts :: String -> [Int]
readInts = map read . words

readVariables :: [String] -> [Int]
readVariables = readInts . drop 2 . head . filter (isPrefixOf "v ")

getModel :: forall i . [Int] -> [(Int, i)] -> [(i, Bool)]
getModel results mapping = mapMaybe render results
  where
    getId :: Int -> Maybe i
    getId result = lookup (abs result) mapping
    pair :: Int -> i -> (i, Bool)
    pair result var = (var, result > 0)
    render :: Int -> Maybe (i, Bool)
    render result = pair result `fmap` getId result
    
