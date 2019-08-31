module Formula where

-- The type parameter represents the type of identifier we want to use
-- to label the variables. For an example, think String or Int.
data Formula i =
  Var i
  | Neg (Formula i)
  | Or  (Formula i) (Formula i)
  | And (Formula i) (Formula i)

-- The following implementation of Show is very inefficient and only
-- intended to debug small examples.

showBinop :: Show i => Formula i -> String -> Formula i -> String
showBinop x op y = '(' : show x ++ spaced ++ show y ++ ")"
  where spaced = ' ' : op ++ [' ']

instance Show i => Show (Formula i) where
  show (Var i)   = show i
  show (Neg x)   = '~' : show x
  show (Or x y)  = showBinop x "or" y
  show (And x y) = showBinop x "and" y


-- Conjunctive normal form.  Inspired by:
-- https://github.com/chris-taylor/aima-haskell/tree/master/src/AI/Logic
