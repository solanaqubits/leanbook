import Verification.QuantumHeterogeneousBBPSSW
open QuantumHeterogeneousBBPSSW QuantumBBPSSWDistillation
open QuantumMixedEnvironment QuantumCentralDepolarization
open QuantumNoisyBellInstrument
open scoped BigOperators ComplexOrder Matrix Kronecker
example (x y : ℝ) : purified (werner x ⊗ₖ werner y) =
    (heteroTargetMass x y : ℂ) • bellProjector .phiPlus +
    ((heteroSuccessProb x y - heteroTargetMass x y : ℝ)/3 : ℂ) •
      (1-bellProjector .phiPlus) := purified_hetero_isotropic x y
example : purified (werner 1 ⊗ₖ werner (-1/2)) ≠ 0 :=
  nonphysical_zero_weight_nonzero_output.2
example :
    ((heteroSuccessProb 0 1 : ℂ)⁻¹ • purified (werner 0 ⊗ₖ werner 1)).PosSemidef ∧
    ((heteroSuccessProb 0 1 : ℂ)⁻¹ • purified (werner 0 ⊗ₖ werner 1)).trace = 1 :=
  purified_hetero_conditional_density (by norm_num) (by norm_num)
example (w : Visibility) (σ : EnvironmentState (Fin 2)) (τ : EnvironmentState (Fin 3)) :
    swapThenPurify w σ τ = (successProbability (swapFidelity w.val) : ℂ) •
      werner (recurrence (swapFidelity w.val)) := swapThenPurify_matrix w σ τ
example (w : Visibility) (σ : EnvironmentState (Fin 2)) (τ : EnvironmentState (Fin 3)) :
    (successProbability (swapFidelity w.val) : ℂ)⁻¹ • swapThenPurify w σ τ =
      werner (recurrence (swapFidelity w.val)) := swapThenPurify_conditional w σ τ
