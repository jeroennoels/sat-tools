module CNF where

import Formula

import Data.Maybe
import Data.List

data Literal i = Positive i | Negative i
  deriving Eq

newtype Clause i = Clause [Literal i]
  deriving Show

var :: Literal i -> i
var (Positive v) = v
var (Negative v) = v

compareLiterals :: Ord i => Literal i -> Literal i -> Ordering
compareLiterals x y | ord /= EQ = ord
  where ord = compare (var x) (var y)
compareLiterals (Negative _) (Positive _) = LT
compareLiterals _ _ = GT

instance Ord i => Ord (Literal i) where
  compare = compareLiterals

instance Show i => Show (Literal i) where
  show (Positive v) = show v
  show (Negative v) = '-' : show v

toLiteral :: Formula i -> Literal i
toLiteral (Var x) = Positive x
toLiteral (Not (Var x)) = Negative x

-- Turn a nested CNF formula into a flat list of clauses.

flattenAnd :: Formula i -> [Clause i]
flattenAnd (And x y) = flattenAnd x ++ flattenAnd y
flattenAnd (Or x y) = [Clause (flattenOr x y)]
flattenAnd x = [Clause [toLiteral x]]

flattenOr :: Formula i -> Formula i -> [Literal i]
flattenOr (Or x y) (Or v w) = flattenOr x y ++ flattenOr v w
flattenOr (Or x y) z = toLiteral z : flattenOr x y
flattenOr z (Or x y) = toLiteral z : flattenOr x y
flattenOr x y = [toLiteral x, toLiteral y]

-- The following assumes the input list is sorted in a specif way.
-- See the Ord instance of Literal

removeTautologies :: Eq i => [Literal i] -> Maybe [Literal i]
removeTautologies (Negative v : Positive w : zs) | v == w = Nothing
removeTautologies (x:y:zs) = (x:) `fmap` removeTautologies (y:zs)
removeTautologies xs = Just xs

normalizeLiterals :: Ord i => [Literal i] -> Maybe [Literal i]
normalizeLiterals = removeTautologies . sort . nub

normalizeClause :: Ord i => Clause i -> Maybe (Clause i)
normalizeClause (Clause xs) = Clause `fmap` normalizeLiterals xs

normalizeClauses :: Ord i => [Clause i] -> [Clause i]
normalizeClauses = mapMaybe normalizeClause
