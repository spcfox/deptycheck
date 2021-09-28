module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{Empty} $ Fuel -> (n : Nat) -> (a : Type) -> Gen (Vect n a)
