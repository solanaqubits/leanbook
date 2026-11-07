import Verification.QuantumBBPSSWConvergence
open QuantumBBPSSWDistillation QuantumBBPSSWConvergence
open scoped BigOperators ComplexOrder Matrix Kronecker

example : treeProbability (1/4) 2 = 1/8 := by
  norm_num [treeProbability_two, recurrence, targetMass, successProbability]
example : treeProbability (1/4) 2 ≠
    successProbability (1/4) * successProbability (recurrence (1/4)) := by
  norm_num [treeProbability_two, recurrence, targetMass, successProbability]
example (F : ℝ) (n : ℕ) : treeProbability F n =
    ∏ k ∈ Finset.range n, successProbability (fidelityOrbit F k) ^ (2 ^ (n-1-k)) :=
  treeProbability_closed_form F n
example (n : ℕ) : 0 < treeProbability 0 n ∧ treeProbability 0 n ≤ 1 :=
  ⟨treeProbability_pos _ _, treeProbability_le_one (by norm_num) _⟩
example (F : ℝ) (n : ℕ) : treeMatrix F n =
    (treeProbability F n : ℂ) • werner (fidelityOrbit F n) := treeMatrix_eq_werner F n
example (n : ℕ) : (treeMatrix 0 n).PosSemidef := treeMatrix_positive (by norm_num) n
example (n : ℕ) : ((treeProbability 0 n : ℂ)⁻¹ • treeMatrix 0 n).PosSemidef :=
  treeMatrix_conditional_positive (by norm_num) n
example (F : ℝ) (n : ℕ) : (treeMatrix F n).trace = (treeProbability F n : ℂ) :=
  treeMatrix_trace F n
example (F : ℝ) (n : ℕ) : ((treeProbability F n : ℂ)⁻¹ • treeMatrix F n).trace = 1 :=
  treeMatrix_conditional_trace F n
example : treeProbability 1 2 = 1 := by
  norm_num [treeProbability_two, recurrence, targetMass, successProbability]
