{-# LANGUAGE ScopedTypeVariables #-}
module Assignment where

import Eval

import Data.Set (Set)
import qualified Data.Set as Set

characteristic :: Ord i => Set i -> Set i -> Assignment i
characteristic dom subset = 
  Assignment { domain = Set.toList dom,
               assign = flip Set.member subset }

allAssignments :: forall i . Ord i => Set i -> [Assignment i]
allAssignments vars = map (characteristic vars) subsets
  where
    subsets :: [Set i]
    subsets = Set.toList (Set.powerSet vars)
