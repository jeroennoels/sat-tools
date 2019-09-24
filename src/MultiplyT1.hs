module MultiplyT1 where

import Formula
import Digits


multiplyDigits :: IdentifyT1 i j => i -> i -> i -> Formula j
multiplyDigits a b c =
  (((posT1 a `And` posT1 b) `Or` (negT1 a `And` negT1 b)) `Implies` posT1 c) `And`
  (((posT1 a `And` negT1 b) `Or` (negT1 a `And` posT1 b)) `Implies` negT1 c) `And`
  ((zeroT1 a `Or` zeroT1 b) `Implies` zeroT1 c)
