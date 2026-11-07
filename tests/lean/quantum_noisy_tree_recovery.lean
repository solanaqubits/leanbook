import Verification.QuantumNoisyBBPSSWTree
open QuantumNoisyBBPSSWTree QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence
open QuantumHeterogeneousBBPSSW QuantumBBPSSWDistillation

example : ∃ n : ℕ, (17 / 20 : ℝ) < noisyOrbit (19 / 20) (73 / 100) n := by
  have h := nineteen_twentieths_four_fifths_recovery_possible
  norm_num [elemFidelity, swapFidelity] at h
  exact h

example (n : ℕ) : noisyOrbit (19 / 20) (343 / 400) n < (37 / 40 : ℝ) := by
  have h := nineteen_twentieths_nine_tenths_below_elem n
  norm_num [elemFidelity, swapFidelity] at h
  exact h

-- The successful existential witness does not assert restoration in one round.
example : noisyOrbit (19 / 20) (73 / 100) 1 < (17 / 20 : ℝ) := by
  norm_num [noisyOrbit, noisyRecurrence, recurrence,
    QuantumBBPSSWDistillation.targetMass, successProbability]

-- Equality with the stationary ceiling is not sufficient for strict recovery.
example (γ w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (hc : criticalGamma < γ) (hγ : γ < 1)
    (hceil : elemFidelity w = upperWindowCeiling γ) :
    ¬ ∃ n : ℕ, elemFidelity w < noisyOrbit γ (swapFidelity w) n := by
  rw [exists_noisy_depth_exceeding_elemFidelity_iff hw0 hw1 hc hγ]
  simp [hceil]

-- A resource exactly at the unstable lower fixed point cannot be improved.
example (γ : ℝ) (hc : criticalGamma < γ) (n : ℕ) :
    noisyOrbit γ (lowerWindowBound γ) n = lowerWindowBound γ :=
  noisyOrbit_fixed ((noisyRecurrence_fixed_points_iff hc).mpr (Or.inr (Or.inl rfl))) n
