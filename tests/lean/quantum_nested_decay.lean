import Verification.QuantumNestedRepeater
open QuantumNestedRepeater QuantumRepeaterChain QuantumCentralDepolarization
open QuantumHeterogeneousBBPSSW Filter Topology

example : nodeVisibilityValue (nodeVisibilityValue (3/5)) < (3/5 : ℝ)^4 :=
  three_fifths_two_step_swap_reversal.2.2.2.2

example (w : Visibility) (h : w.val < 1) :
    Tendsto (fun k => (visibilityAt w k).val) atTop (nhds 0) :=
  visibilityAt_tendsto_zero w h

example (w : Visibility) (h : w.val < 1) :
    Tendsto (fun k => elemFidelity (visibilityAt w k).val) atTop (nhds (1/4)) :=
  elemFidelity_visibilityAt_tendsto_quarter w h

example : (4/5 : ℝ)^2 < nodeVisibilityValue (4/5) ∧ nodeVisibilityValue (4/5) < 4/5 :=
  nodeVisibilityValue_between_sq_and_self (by norm_num) (by norm_num) (by norm_num)

example : nodeVisibilityValue (3/5) ^ 2 < (1/3 : ℝ) := by
  norm_num [nodeVisibilityValue]

example : nodeVisibilityValue 0 = 0 ∧ nodeVisibilityValue 1 = 1 := by
  norm_num [nodeVisibilityValue]
