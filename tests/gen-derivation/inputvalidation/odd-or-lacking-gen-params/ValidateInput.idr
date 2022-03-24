module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

%default total

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Unrelated stuff in the resulting dpair ---

genY_with_unrelated : Fuel -> (a : Type) -> Gen (b : Type ** n : Nat ** Y a b)
genY_with_unrelated = deriveGen

genY_with_repeating_name_equityped : Fuel -> (a : Type) -> Gen (b : Type ** b : Type ** Y a b)
genY_with_repeating_name_equityped = deriveGen

genY_with_repeating_name_difflytyped : Fuel -> (a : Type) -> Gen (b : Type ** b : Nat ** Y a b)
genY_with_repeating_name_difflytyped = deriveGen

genY_with_repeating_name_difflytyped' : Fuel -> (a : Type) -> Gen (b : Nat ** b : Type ** Y a b)
genY_with_repeating_name_difflytyped' = deriveGen

--- Not all arguments are used ---

genY_unused_argument : Fuel -> (a, b : Type) -> (c : Nat) -> Gen $ Y a b
genY_unused_argument = deriveGen