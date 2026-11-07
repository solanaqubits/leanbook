import Verification.QuantumNoisyBBPSSW
open QuantumNoisyBBPSSW

example {γ F : ℝ} (h0 : 0 ≤ γ) (hc : γ < criticalGamma) :
    noisyRecurrence γ F = F ↔ F = 1/4 := noisyRecurrence_subcritical_fixed_iff h0 hc F

example {F : ℝ} (hF : 1 / 4 < F) : noisyRecurrence (9/10) F < F :=
  nine_tenths_no_working_window hF

example (F : ℝ) : noisyRecurrence criticalGamma F = F ↔
    F = 1/4 ∨ F = (2*criticalGamma+1)/4 := noisyRecurrence_critical_fixed_iff F

example {F : ℝ} (hF : 1 / 4 ≤ F) : noisyRecurrence criticalGamma F ≤ F :=
  noisyRecurrence_critical_no_strict_gain hF

example {γ F : ℝ} (hc : criticalGamma < γ) (h1 : γ < 1) (hF : 1 / 4 < F) :
    F < noisyRecurrence γ F ↔ lowerWindowBound γ < F ∧ F < upperWindowCeiling γ :=
  noisyRecurrence_strict_improve_iff_in_window hc h1 hF

example : lowerWindowBound criticalGamma = upperWindowCeiling criticalGamma := by
  rw [critical_window_bounds_coincide.1, critical_window_bounds_coincide.2]
