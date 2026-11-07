import Verification.QuantumNoisyBBPSSWConvergence
open QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence Filter Topology

example (γ : ℝ) (hc : criticalGamma < γ) (n : ℕ) :
    noisyOrbit γ (1 / 4) n = 1 / 4 ∧
    noisyOrbit γ (lowerWindowBound γ) n = lowerWindowBound γ ∧
    noisyOrbit γ (upperWindowCeiling γ) n = upperWindowCeiling γ := by
  refine ⟨noisyOrbit_fixed (noisyRecurrence_quarter γ) n, ?_, ?_⟩
  · exact (noisyOrbit_stationary_iff hc).mpr (Or.inr (Or.inl rfl)) n
  · exact (noisyOrbit_stationary_iff hc).mpr (Or.inr (Or.inr rfl)) n

example {γ F : ℝ} (hc : criticalGamma < γ) (h1 : γ < 1)
    (h0 : 0 ≤ F) (hq : F < 1 / 4) (n : ℕ) :
    0 ≤ noisyOrbit γ F n ∧ noisyOrbit γ F n < 1 / 4 :=
  noisyOrbit_below_quarter hc h1 h0 hq n

example {γ F : ℝ} (hc : criticalGamma < γ) (h1 : γ < 1)
    (hl : lowerWindowBound γ < F) (hu : F < upperWindowCeiling γ) (n : ℕ) :
    lowerWindowBound γ < noisyOrbit γ F n ∧
    noisyOrbit γ F n < upperWindowCeiling γ :=
  noisyOrbit_inside_window hc h1 hl hu n
