module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%language ElabReflection

f : Nat -> Nat
f = (+2)

g : {n : _} -> Fin n -> Fin n
g = finS

data Y : (n : Nat) -> Fin (f n) -> Type where
  Y0 : Y 0 i
  Y2 : Y 2 2

data Z : Type where
  MkZ : (n : Nat) -> (x : Fin (f n)) -> (y : Y n (g x)) -> Z

%hint ShowY : Show (Y n i); ShowY = %runElab derive
%hint ShowZ : Show Z; ShowZ = %runElab derive

checkedGen : Fuel -> Gen MaybeEmpty Z
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
