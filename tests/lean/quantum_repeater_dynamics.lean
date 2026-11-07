import Verification.QuantumRepeaterChain
open QuantumRepeaterChain QuantumHeterogeneousBBPSSW QuantumCentralDepolarization
example : nodeVisibilityValue (4/5) = 608/881 ∧ nodeProbability (4/5) = 881/1250 := by
  norm_num [nodeVisibilityValue, nodeProbability]
example : (608/881:ℝ) < 4/5 := by norm_num
example : nodeVisibilityValue 0 = 0 ∧ nodeVisibilityValue 1 = 1 := by
  norm_num [nodeVisibilityValue]
example (w : Visibility) : Antitone (fun k => (visibilityAt w k).val) := visibilityAt_antitone w
example {w : Visibility} (h0 : 0 < w.val) (h1 : w.val < 1) :
    StrictAnti (fun k => (visibilityAt w k).val) := visibilityAt_strictAnti h0 h1
example (w : Visibility) (k : ℕ) :
    elemFidelity (visibilityAt w (k+1)).val ≤ elemFidelity (visibilityAt w k).val :=
  fidelityAt_nonincrease w k
example (w : Visibility) (k : ℕ) : (visibilityAt w (k+1)).val =
    2*(visibilityAt w k).val^2*(1+2*(visibilityAt w k).val^2)/
      (3*(1+(visibilityAt w k).val^4)) := visibilityAt_recurrence w k
