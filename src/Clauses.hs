{-# LANGUAGE DeriveFunctor #-}
module Clauses (
  Literal (..), Clause(..),
  literals,
  distinctVariables, normalizeClauses,
  formulaToClauses) where

import Formula

import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

data Literal i = Positive i | Negative i
  deriving (Eq, Functor)

newtype Clause i = Clause [Literal i]
  deriving (Eq, Ord, Functor, Show)

literals :: Clause i -> [Literal i]
literals (Clause lits) = lits

var :: Literal i -> i
var (Positive v) = v
var (Negative v) = v

pos :: Literal i -> Bool
pos (Positive v) = True
pos (Negative v) = False

compareLiterals :: Ord i => Literal i -> Literal i -> Ordering
compareLiterals x y
  | compareVars == EQ = compare (pos x) (pos y)
  | otherwise = compareVars
  where
    compareVars = compare (var x) (var y)

instance Ord i => Ord (Literal i) where
  compare = compareLiterals

instance Show i => Show (Literal i) where
  show (Positive v) = show v
  show (Negative v) = '-' : show v

toLiteral :: Formula i -> Literal i
toLiteral (Var x) = Positive x
toLiteral (Not (Var x)) = Negative x

variablesInClause :: Ord i => Clause i -> Set i
variablesInClause (Clause xs) = Set.fromList $ map var xs

distinctVariables :: Ord i => [Clause i] -> Set i
distinctVariables = Set.unions . map variablesInClause


-- Now we convert a nested a CNF formula into a flat list of clauses.
-- The implementation assumes the input is already in CNF.  We use
-- naive recursion which may not be very efficient, but that is good
-- enough for now.

flattenCNF :: Formula i -> [Clause i]
flattenCNF (And x y) = flattenCNF x ++ flattenCNF y
flattenCNF (Or x y) = [Clause (flattenOr x y)]
flattenCNF x = [Clause [toLiteral x]]

flattenOr :: Formula i -> Formula i -> [Literal i]
flattenOr (Or x y) (Or v w) = flattenOr x y ++ flattenOr v w
flattenOr (Or x y) z = toLiteral z : flattenOr x y
flattenOr z (Or x y) = toLiteral z : flattenOr x y
flattenOr x y = [toLiteral x, toLiteral y]

-- The following assumes the list of literals is ordered in such a way
-- that opposite literals are adjacent, specifically as defined by the
-- instance declaration for (Ord Literal).

removeTautologies :: Eq i => [Literal i] -> Maybe [Literal i]
removeTautologies (Negative v : Positive w : zs) | v == w = Nothing
removeTautologies (x:y:zs) = (x:) `fmap` removeTautologies (y:zs)
removeTautologies xs = Just xs

normalizeLiterals :: Ord i => [Literal i] -> Maybe [Literal i]
normalizeLiterals = removeTautologies . sort . nub

normalizeClause :: Ord i => Clause i -> Maybe (Clause i)
normalizeClause (Clause xs) = Clause `fmap` normalizeLiterals xs

normalizeClauses :: Ord i => [Clause i] -> [Clause i]
normalizeClauses = sort . nub . mapMaybe normalizeClause

formulaToClauses :: Ord i => Formula i -> [Clause i]
formulaToClauses = normalizeClauses . flattenCNF . toCNF
