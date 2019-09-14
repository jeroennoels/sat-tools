{-# LANGUAGE ScopedTypeVariables #-}
module Dimacs where

import Clauses
import Data.List (intercalate)
import Data.Map.Strict (Map, (!))
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

toDimacsLines :: Ord i => [Clause i] -> [String]
toDimacsLines clauses = header : map (clauseToDimacs enum) clauses
  where enum = enumerateVariables clauses
        header = "p cnf " ++ show (length enum) ++ " " ++ show (length clauses)

dimacsOutput :: Ord i => [Clause i] -> IO ()
dimacsOutput = sequence_ . map putStrLn . toDimacsLines
