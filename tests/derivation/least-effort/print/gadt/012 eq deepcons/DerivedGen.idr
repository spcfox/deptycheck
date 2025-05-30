module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : x `LT2` S (S x)
  Step : x `LT2` y -> x `LT2` S y

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a : Nat) -> Gen MaybeEmpty (b ** LT2 a b)
