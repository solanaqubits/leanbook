import Verification.QuantumRepeaterChain
open QuantumRepeaterChain QuantumCentralDepolarization QuantumNoisyVisibility
open scoped BigOperators ComplexOrder Matrix Kronecker
example (w : Visibility) (k : ℕ) :
    repeaterMatrix w k = (repeaterProbability w k : ℂ) • isotropic (visibilityAt w k) :=
  repeaterMatrix_refinement w k
example (w : Visibility) (k : ℕ) : (repeaterMatrix w k).PosSemidef :=
  repeaterMatrix_positive w k
example (w : Visibility) (k : ℕ) : (repeaterMatrix w k).trace = (repeaterProbability w k : ℂ) :=
  repeaterMatrix_trace w k
example (w : Visibility) (k : ℕ) :
    let M := (repeaterProbability w k : ℂ)⁻¹ • repeaterMatrix w k
    M.PosSemidef ∧ M.trace = 1 := repeaterMatrix_conditional_density w k
example (w : Visibility) (k : ℕ) :
    0 < repeaterProbability w k ∧ repeaterProbability w k ≤ 1 :=
  ⟨repeaterProbability_pos w k, repeaterProbability_le_one w k⟩
example (w : Visibility) (k : ℕ) : repeaterProbability w k =
    ∏ j ∈ Finset.range k, nodeProbability (visibilityAt w j).val ^ (4^(k-1-j)) :=
  repeaterProbability_closed_form w k
example : repeaterProbability ⟨0, le_rfl, by norm_num⟩ 2 = 1/32 := by
  norm_num [repeaterProbability, nodeProbability, visibilityAt, nodeVisibility, nodeVisibilityValue]
example : repeaterProbability ⟨1, by norm_num, le_rfl⟩ 2 = 1 := by
  norm_num [repeaterProbability, nodeProbability, visibilityAt, nodeVisibility, nodeVisibilityValue]
example : segmentCount 2 = 4 ∧ rawPairCount 2 = 16 := by
  norm_num [segmentCount, rawPairCount]
example (k : ℕ) : rawPairCount k = segmentCount k * 2^k := rawPairCount_per_segment k
