import Verification.MlDsaPackedPredicate
open MlDsaPackedPredicate
example : pt5 8380416 0 8380416 0 0 = 0 := by decide
example : pt5 8380417 0 0 0 0 ≠ 0 := by decide
example : pt5 8388607 0 0 0 0 ≠ 0 := by decide
example : pt5 16777215 0 0 0 0 = 0 ∧ ¬ (16777215 < 8380417) :=
  counterexample_without_23_bit_premise
example (a b c : Nat) : ∀ x ∈ unpack8 a b c 64, x < 8388608 :=
  unpack8_high_bounded a b c
