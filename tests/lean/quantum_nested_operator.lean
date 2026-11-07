import Verification.QuantumNestedRepeater
open QuantumNestedRepeater QuantumRepeaterChain QuantumCentralDepolarization
open QuantumBellDiagonalSwapping QuantumBBPSSWConvergence QuantumBBPSSWDistillation
open QuantumHeterogeneousBBPSSW QuantumBellDiagonalInputs
open scoped ComplexOrder Matrix Kronecker

example (m k : ℕ) (w : Visibility) :
    nestedRepeaterMatrix m w k =
      (nestedRepeaterProbability m w k : ℂ) •
        QuantumNoisyVisibility.isotropic (nestedVisibilityAt m w k) :=
  nestedRepeaterMatrix_refinement m w k

example (m k : ℕ) (w : Visibility) :
    (nestedRepeaterMatrix m w k).PosSemidef ∧
    (nestedRepeaterMatrix m w k).trace = (nestedRepeaterProbability m w k : ℂ) :=
  ⟨nestedRepeaterMatrix_positive m w k, nestedRepeaterMatrix_trace m w k⟩

example (m k : ℕ) (w : Visibility) :
    0 < nestedRepeaterProbability m w k ∧ nestedRepeaterProbability m w k ≤ 1 :=
  ⟨nestedRepeaterProbability_pos m w k, nestedRepeaterProbability_le_one m w k⟩

example (m k : ℕ) (w : Visibility) :
    let D := (nestedRepeaterProbability m w k : ℂ)⁻¹ • nestedRepeaterMatrix m w k
    D.PosSemidef ∧ D.trace = 1 := nestedRepeaterMatrix_conditional_density m w k

example (w : Visibility) (k : ℕ) :
    nestedRepeaterMatrix 1 w k = repeaterMatrix w k ∧
    nestedRepeaterProbability 1 w k = repeaterProbability w k :=
  ⟨nestedRepeaterMatrix_one w k, nestedRepeaterProbability_one w k⟩

example (w : Visibility) (k : ℕ) :
    (nestedVisibilityAt 0 w k).val = w.val^(2^k) ∧
    nestedRepeaterProbability 0 w k = 1 :=
  ⟨nestedVisibilityAt_zero w k, nestedRepeaterProbability_zero w k⟩

private def zeroVisibility : Visibility := ⟨0, by norm_num, by norm_num⟩

example : nestedRepeaterProbability 2 zeroVisibility 2 = (1/134217728 : ℝ) := by
  norm_num [nestedRepeaterProbability, nestedBranchFactor, nestedNodeProbability,
    nestedVisibilityAt, nestedNodeVisibility, nestedNodeVisibilityValue, zeroVisibility,
    treeProbability, fidelityOrbit, Function.iterate_succ_apply', swapFidelity,
    recurrence, QuantumBBPSSWDistillation.targetMass, successProbability]
