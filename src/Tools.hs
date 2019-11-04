{-# LANGUAGE ScopedTypeVariables #-}
module Tools where

import Formula
import Clauses
import Data.List (concatMap, nub)

newtype Bit = Bit Int
  deriving (Eq, Ord, Read, Show)

-- Two bits means 4 colors, three bits gives 8 colors, etc.
bitPositions :: [Bit]
bitPositions = [Bit 0, Bit 1]

data VertexColorBit = VertexColorBit Int Bit
  deriving (Eq, Ord, Read, Show)

-- quick hack, assuming 2 bits and thus a priori 4 colors
onlyThreeColors :: Int -> Formula VertexColorBit
onlyThreeColors x =
  Var (VertexColorBit x (Bit 0)) `Or` Var (VertexColorBit x (Bit 1))

differentBits :: Int -> Int -> Bit -> Formula VertexColorBit
differentBits x y bit = Not $
  Var (VertexColorBit x bit) `Equiv` Var (VertexColorBit y bit)

differentColors :: (Int, Int) -> Formula VertexColorBit
differentColors (x,y) = disjunction $ map (differentBits x y) bitPositions

vertices :: [(Int, Int)] -> [Int]
vertices edges = nub (map fst edges ++ map snd edges)

graphColoring :: [(Int, Int)] -> [Clause VertexColorBit]
graphColoring edges =
  concatMap (formulaToClauses . differentColors) edges ++
  concatMap (formulaToClauses . onlyThreeColors) (vertices edges)

graph :: [(Int, Int)]
graph = completeGraph 4

completeGraph :: Int -> [(Int, Int)]
completeGraph n = [(x,y) | x <- [1..n], y <- [1..n], x < y]
