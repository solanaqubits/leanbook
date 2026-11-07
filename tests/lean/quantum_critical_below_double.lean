import Verification.QuantumNoisyBBPSSWCritical
open QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence QuantumNoisyBBPSSWCritical
open Filter Topology

example : criticalFidelity = (3 * Real.sqrt 5 - 1) / 8 ∧
    (7 / 10 : ℝ) < criticalFidelity ∧ criticalFidelity < 3 / 4 := by
  refine ⟨criticalFidelity_radical, ?_, ?_⟩
  · unfold criticalFidelity
    linarith [nine_tenths_below_critical]
  · unfold criticalFidelity
    linarith [criticalGamma_bounds.2]

example : StrictMono (noisyOrbit criticalGamma 0) ∧
    Tendsto (noisyOrbit criticalGamma 0) atTop (nhds (1 / 4)) := by
  exact ⟨lowOrbit_strictMono (by linarith [criticalGamma_bounds.1])
      criticalGamma_bounds.2 (by norm_num) (by norm_num),
    criticalOrbit_tendsto_quarter (by norm_num) (by linarith [criticalFidelity_bounds.1])⟩

example : StrictAnti (noisyOrbit criticalGamma (1 / 2)) ∧
    Tendsto (noisyOrbit criticalGamma (1 / 2)) atTop (nhds (1 / 4)) :=
  ⟨criticalOrbit_strictAnti_below_double (by norm_num) criticalFidelity_bounds.1,
    criticalOrbit_tendsto_quarter (by norm_num) criticalFidelity_bounds.1⟩

example (n : ℕ) : 1 / 4 < noisyOrbit criticalGamma (1 / 2) n ∧
    noisyOrbit criticalGamma (1 / 2) n < criticalFidelity :=
  criticalOrbit_below_double (by norm_num) criticalFidelity_bounds.1 n
