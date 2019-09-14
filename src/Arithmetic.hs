module Arithmetic where

import Formula

-- Plus or Minus
data Sign i = P i | M i deriving (Eq, Ord, Show)

plus :: i -> Formula (Sign i)
plus v = Var (P v)

mins :: i -> Formula (Sign i)
mins v = Var (M v)

-- The sign of a ternary digit cannot simultaneously be plus and minus.
isDigit :: i -> Formula (Sign i)
isDigit v = Not (plus v `And` mins v)

multiplyDigits :: i -> i -> i -> Formula (Sign i)
multiplyDigits a b c =
  isDigit a `And` isDigit b `And` isDigit c `And`
  (((plus a `And` plus b) `Or` (mins a `And` mins b)) `Equiv` plus c) `And`
  (((plus a `And` mins b) `Or` (mins a `And` plus b)) `Equiv` mins c)
