import Verification.QuantumNoisyBBPSSWTree
open QuantumNoisyBBPSSWTree QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence
open QuantumBBPSSWDistillation QuantumBBPSSWConvergence QuantumCentralDepolarization

example (γ : ℝ) : noisyTreeProbability γ (1 / 4) 2 = 1 / 8 ∧
    noisyTreeProbability γ (1 / 4) 3 = 1 / 128 := by
  norm_num [noisyTreeProbability_quarter]

example : noisyTreeProbability (19 / 20) (3 / 4) 1 = 13 / 18 ∧
    noisyTreeProbability (19 / 20) (3 / 4) 2 = 27857 / 72900 := by
  norm_num [noisyTreeProbability, noisyOrbit, noisyRecurrence, recurrence,
    QuantumBBPSSWDistillation.targetMass, successProbability]

example : noisyTreeProbability 0 1 2 = 1 / 2 ∧ noisyTreeProbability 1 1 2 = 1 := by
  norm_num [noisyTreeProbability, noisyOrbit, noisyRecurrence, recurrence,
    QuantumBBPSSWDistillation.targetMass, successProbability]

example : 0 < noisyTreeProbability (-2) (-3) 3 := noisyTreeProbability_pos _ _ _

example (γ : Visibility) (F : ℝ) (h : 0 ≤ F ∧ F ≤ 1) (n : ℕ) :
    0 < noisyTreeProbability γ.val F n ∧ noisyTreeProbability γ.val F n ≤ 1 :=
  ⟨noisyTreeProbability_pos _ _ _, noisyTreeProbability_le_one γ h.1 h.2 n⟩

example (F : ℝ) (n : ℕ) : noisyTreeMatrix unitVisibility F n = treeMatrix F n :=
  noisyTreeMatrix_unit F n

example (F : ℝ) (n : ℕ) :
    (noisyTreeProbability 0 F (n + 1) : ℂ)⁻¹ • noisyTreeMatrix zeroVisibility F (n + 1) =
      werner (1 / 4) := noisyTreeMatrix_zero_conditional F (Nat.succ_pos n)
