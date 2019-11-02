{-# LANGUAGE ScopedTypeVariables #-}
module Tools where

import Formula
import Clauses

newtype Bit = Bit Int
  deriving (Eq, Ord, Read, Show)

bitPositions :: [Bit]
bitPositions = [Bit 0, Bit 1]

data VertexColorBit = VertexColorBit Int Bit
  deriving (Eq, Ord, Read, Show)

differentBits :: Int -> Int -> Bit -> Formula VertexColorBit
differentBits x y bit = Not $
  Var (VertexColorBit x bit) `Equiv` Var (VertexColorBit y bit)
  
differentColors :: Int -> Int -> Formula VertexColorBit
differentColors x y = undefined
  
