import Verification.QuantumNoisyBBPSSW
open QuantumNoisyBBPSSW QuantumBBPSSWDistillation

example (F : ℝ) : noisyRecurrence 1 F = recurrence F ∧ noisyRecurrence 0 F = 1/4 :=
  ⟨noisyRecurrence_one F, noisyRecurrence_zero F⟩

example : lowerWindowBound 1 = (1/2 : ℝ) ∧ upperWindowCeiling 1 = 1 := by
  norm_num [lowerWindowBound, upperWindowCeiling, noisyDiscFactor]

example : noisyRecurrence (19/20) (3/4) = (99/130 : ℝ) ∧
    (3/4 : ℝ) < noisyRecurrence (19/20) (3/4) :=
  ⟨nineteen_twentieths_working_window_witness.1,
    nineteen_twentieths_working_window_witness.2.1⟩

example : upperWindowCeiling (19/20) = (29+Real.sqrt 31)/40 := nineteen_twentieths_ceiling

example : noisyRecurrence (19/20) (upperWindowCeiling (19/20)) =
    upperWindowCeiling (19/20) :=
  (noisyRecurrence_fixed_points_iff nineteen_twentieths_above_critical).mpr
    (Or.inr (Or.inr rfl))

example : upperWindowCeiling (19/20) < noisyRecurrence (19/20) 1 ∧
    noisyRecurrence (19/20) 1 < 1 :=
  ceiling_lt_pure_output nineteen_twentieths_above_critical (by norm_num)

example : lowerWindowBound (19/20) < (3/4 : ℝ) ∧
    (3/4 : ℝ) < upperWindowCeiling (19/20) :=
  (noisyRecurrence_strict_improve_iff_in_window nineteen_twentieths_above_critical
    (by norm_num) (by norm_num)).mp nineteen_twentieths_working_window_witness.2.1
