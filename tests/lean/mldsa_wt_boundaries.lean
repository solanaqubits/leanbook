import Verification.MlDsaWtBranch
open MlDsaWtBranch
example : (¬ (8380416 / 256 < 32736)) ∧ 8380416 < 8380417 := by decide
example (c : Nat) (hc : c < 8388608) :
    ((¬ c / 256 < 32736) ∧ c < 8380417) ↔ c = 8380416 :=
  split_c5_false_positive_iff c hc
example (part full : Nat) (hp : part < 8388608) (valid : Prop)
    (hclear : part = 0 → valid) :
    (part + 8388608 * full < 8388608 ∧
      (part + 8388608 * full = 0 ∨ valid)) ↔ full = 0 ∧ valid :=
  repair_low_exact part full hp valid hclear
-- Without the clear-part premise the repair equivalence is false.
example : ¬ (((0 : Nat) + 8388608 * 0 < 8388608 ∧
    ((0 : Nat) + 8388608 * 0 = 0 ∨ False)) ↔ (0 : Nat) = 0 ∧ False) := by decide
example : [0, 8380416, 0].filter (fun x : Nat => decide (x < 8380417)) =
    [0, 8380416, 0] := by decide
