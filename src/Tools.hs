{-# LANGUAGE ScopedTypeVariables #-}
module Tools where

import Formula
import Clauses
import Data.List (concatMap)

newtype Bit = Bit Int
  deriving (Eq, Ord, Read, Show)

-- Two bits means 4 colors, three bits gives 8 colors, etc.
bitPositions :: [Bit]
bitPositions = [Bit 0, Bit 1]

data VertexColorBit = VertexColorBit Int Bit
  deriving (Eq, Ord, Read, Show)

differentBits :: Int -> Int -> Bit -> Formula VertexColorBit
differentBits x y bit = Not $
  Var (VertexColorBit x bit) `Equiv` Var (VertexColorBit y bit)
  
differentColors :: (Int, Int) -> Formula VertexColorBit
differentColors (x,y) = disjunction $ map (differentBits x y) bitPositions
  
graphColoring :: [(Int, Int)] -> [Clause VertexColorBit]
graphColoring edges = concatMap (formulaToClauses . differentColors) edges

graph :: [(Int, Int)]
graph = completeGraph 4

completeGraph :: Int -> [(Int, Int)]
completeGraph n = [(x,y) | x <- [1..n], y <- [1..n], x < y]
