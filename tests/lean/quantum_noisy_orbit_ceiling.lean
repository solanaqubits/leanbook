import Verification.QuantumNoisyBBPSSWConvergence
open QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence Filter Topology

example : StrictMono (noisyOrbit (19 / 20) (3 / 4)) ∧
    Tendsto (noisyOrbit (19 / 20) (3 / 4)) atTop
      (nhds ((29 + Real.sqrt 31) / 40)) := by
  have hc := nineteen_twentieths_above_critical
  have hw := (noisyRecurrence_strict_improve_iff_in_window hc (by norm_num)
    (show (1 / 4 : ℝ) < 3 / 4 by norm_num)).mp
      nineteen_twentieths_working_window_witness.2.1
  refine ⟨noisyOrbit_strictMono_inside_window hc (by norm_num) hw.1 hw.2, ?_⟩
  rw [← nineteen_twentieths_ceiling]
  exact noisyOrbit_tendsto_ceiling hc (by norm_num) hw.1 (by norm_num)

example : StrictAnti (noisyOrbit (19 / 20) 1) ∧
    Tendsto (noisyOrbit (19 / 20) 1) atTop (nhds (upperWindowCeiling (19 / 20))) := by
  have hc := nineteen_twentieths_above_critical
  have hb := working_window_inside_half_one hc (by norm_num)
  exact ⟨noisyOrbit_strictAnti_above_ceiling hc (by norm_num) hb.2.2 le_rfl,
    noisyOrbit_tendsto_ceiling hc (by norm_num) (lt_trans hb.2.1 hb.2.2) le_rfl⟩

example (n : ℕ) : upperWindowCeiling (19 / 20) < noisyOrbit (19 / 20) 1 n := by
  have hc := nineteen_twentieths_above_critical
  have hb := working_window_inside_half_one hc (by norm_num)
  exact (noisyOrbit_above_ceiling hc (by norm_num) hb.2.2 le_rfl n).1
