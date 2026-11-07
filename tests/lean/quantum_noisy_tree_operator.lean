import Verification.QuantumNoisyBBPSSWTree
open QuantumNoisyBBPSSWTree QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence
open QuantumBBPSSWDistillation QuantumBBPSSWConvergence QuantumCentralDepolarization
open QuantumEntanglementSwappingPurificationContract QuantumHeterogeneousBBPSSW
open scoped ComplexOrder Matrix Kronecker

example (γ : Visibility) (F : ℝ) (n : ℕ) :
    noisyTreeMatrix γ F n =
      (noisyTreeProbability γ.val F n : ℂ) • werner (noisyOrbit γ.val F n) :=
  noisyTreeMatrix_eq_werner γ F n

example (γ : Visibility) (n : ℕ) : (noisyTreeMatrix γ 0 n).PosSemidef :=
  noisyTreeMatrix_posSemidef γ (by norm_num) (by norm_num) n

example (γ : Visibility) (F : ℝ) (h : 0 ≤ F ∧ F ≤ 1) (n : ℕ) :
    let D := (noisyTreeProbability γ.val F n : ℂ)⁻¹ • noisyTreeMatrix γ F n
    D.PosSemidef ∧ D.trace = 1 := noisyTreeMatrix_conditional_density γ h.1 h.2 n

example (γ w : Visibility) (n : ℕ) :
    swapThenNoisyTree γ w n =
      (noisyTreeProbability γ.val (swapFidelity w.val) n : ℂ) •
        werner (noisyOrbit γ.val (swapFidelity w.val) n) :=
  swapThenNoisyTree_refinement γ w n

example (γ w : Visibility) (n : ℕ) :
    (swapThenNoisyTree γ w n).trace =
      (noisyTreeProbability γ.val (swapFidelity w.val) n : ℂ) := by
  rw [swapThenNoisyTree_eq_noisyTreeMatrix, noisyTreeMatrix_trace]

example : swapThenNoisyTreeRawPairs 4 = 32 := by
  norm_num [swapThenNoisyTreeRawPairs_eq]
