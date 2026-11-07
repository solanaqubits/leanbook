import Verification.QuantumNoisyBBPSSWCritical
open QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence QuantumNoisyBBPSSWCritical
open Filter Topology

example : StrictAnti (noisyOrbit criticalGamma 1) ∧
    Tendsto (noisyOrbit criticalGamma 1) atTop (nhds ((3 * Real.sqrt 5 - 1) / 8)) := by
  refine ⟨criticalOrbit_strictAnti_above_double criticalFidelity_bounds.2 le_rfl, ?_⟩
  rw [← criticalFidelity_radical]
  exact criticalOrbit_tendsto_double criticalFidelity_bounds.2.le le_rfl

example (n : ℕ) : criticalFidelity < noisyOrbit criticalGamma 1 n :=
  (criticalOrbit_above_double criticalFidelity_bounds.2 le_rfl n).1

example (n : ℕ) : noisyOrbit criticalGamma criticalFidelity n = criticalFidelity ∧
    noisyOrbit criticalGamma (1 / 4) n = 1 / 4 :=
  ⟨(critical_stationary_iff criticalFidelity).mpr (Or.inr rfl) n,
    (critical_stationary_iff (1 / 4)).mpr (Or.inl rfl) n⟩

example : Tendsto (noisyOrbit criticalGamma criticalFidelity) atTop
    (nhds criticalFidelity) :=
  criticalOrbit_tendsto_double le_rfl criticalFidelity_bounds.2.le

example : Tendsto (noisyOrbit criticalGamma (1 / 4)) atTop (nhds (1 / 4)) :=
  criticalOrbit_tendsto_quarter (by norm_num) (by linarith [criticalFidelity_bounds.1])
