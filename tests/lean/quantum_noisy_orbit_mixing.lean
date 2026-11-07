import Verification.QuantumNoisyBBPSSWConvergence
open QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence Filter Topology

example : StrictMono (noisyOrbit (19 / 20) 0) ∧
    Tendsto (noisyOrbit (19 / 20) 0) atTop (nhds (1 / 4)) := by
  have hc := nineteen_twentieths_above_critical
  have hb := working_window_inside_half_one hc (by norm_num)
  exact ⟨noisyOrbit_strictMono_below_quarter hc (by norm_num) (by norm_num) (by norm_num),
    noisyOrbit_tendsto_quarter hc (by norm_num) (by norm_num) (by linarith [hb.1])⟩

example (n : ℕ) :
    1 / 4 < noisyOrbit (19 / 20) (1 / 2) n ∧
    noisyOrbit (19 / 20) (1 / 2) n < lowerWindowBound (19 / 20) := by
  have hc := nineteen_twentieths_above_critical
  have hb := working_window_inside_half_one hc (by norm_num)
  exact noisyOrbit_between_quarter_and_lower hc (by norm_num) (by norm_num) hb.1 n

example : StrictAnti (noisyOrbit (19 / 20) (1 / 2)) ∧
    Tendsto (noisyOrbit (19 / 20) (1 / 2)) atTop (nhds (1 / 4)) := by
  have hc := nineteen_twentieths_above_critical
  have hb := working_window_inside_half_one hc (by norm_num)
  exact ⟨noisyOrbit_strictAnti_between_quarter_and_lower hc (by norm_num)
      (by norm_num) hb.1,
    noisyOrbit_tendsto_quarter hc (by norm_num) (by norm_num) hb.1⟩
