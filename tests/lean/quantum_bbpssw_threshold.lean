import Verification.QuantumBBPSSWDistillation
open QuantumBBPSSWDistillation
example : recurrence 0 = 1 / 5 := by
  norm_num [recurrence, targetMass, successProbability]
example : recurrence (1 / 4) = 1 / 4 ∧ recurrence (1 / 2) = 1 / 2 ∧ recurrence 1 = 1 := by
  norm_num [recurrence, targetMass, successProbability]
example : successProbability (3 / 4) = 13 / 18 ∧ recurrence (3 / 4) = 41 / 52 := by
  norm_num [recurrence, targetMass, successProbability]
example : (3 / 4 : ℝ) < recurrence (3 / 4) :=
  improves_above_threshold _ (by norm_num)
example : recurrence (3 / 8) < (3 / 8 : ℝ) :=
  decreases_between_fixed_points _ (by norm_num)
example : (1 / 8 : ℝ) < recurrence (1 / 8) := improves_below_quarter _ (by norm_num)
example (F : ℝ) : 0 < successProbability F := probability_positive F
