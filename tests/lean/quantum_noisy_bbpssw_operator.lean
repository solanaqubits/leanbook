import Verification.QuantumNoisyBBPSSW
open QuantumNoisyBBPSSW QuantumBBPSSWDistillation QuantumCentralDepolarization
open QuantumEntanglementSwappingPurificationContract QuantumRectangularSwapping
open QuantumCorrelatedMemoryBSM
open scoped ComplexOrder Matrix Kronecker

example (γ : Visibility) : IsCPMap (noisyPurified γ) := noisyPurified_isCPMap γ

example (γ : Visibility) (M : FourDensity) (hM : M.PosSemidef) :
    (noisyPurified γ M).PosSemidef ∧ (noisyPurified γ M).trace = (purified M).trace :=
  ⟨noisyPurified_posSemidef γ hM, noisyPurified_trace γ M⟩

example (γ : Visibility) (M N : FourDensity) (c : ℂ) :
    noisyPurified γ (c • M + N) = c • noisyPurified γ M + noisyPurified γ N := by
  rw [noisyPurified_add, noisyPurified_smul]

example (γ : Visibility) :
    noisyPurified γ (werner 0 ⊗ₖ werner 0) =
      (successProbability 0 : ℂ) • werner (noisyRecurrence γ.val 0) :=
  noisyPurified_werner γ 0

example (γ : Visibility) :
    let D := (successProbability 0 : ℂ)⁻¹ • noisyPurified γ (werner 0 ⊗ₖ werner 0)
    D.PosSemidef ∧ D.trace = 1 := noisyPurified_conditional_density γ (by norm_num)

private def zeroVisibility : Visibility := ⟨0, by norm_num, by norm_num⟩

example (F : ℝ) :
    (successProbability F : ℂ)⁻¹ • noisyPurified zeroVisibility (werner F ⊗ₖ werner F) =
      werner (1/4) := by
  rw [noisyPurified_conditional]
  exact congrArg werner (noisyRecurrence_zero F)

example (γ : Visibility) (F : ℝ) :
    (noisyPurified γ (werner F ⊗ₖ werner F)).trace = (successProbability F : ℂ) :=
  noisyPurified_success_probability γ F
