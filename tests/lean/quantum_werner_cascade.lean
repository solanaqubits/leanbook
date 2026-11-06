import Verification.QuantumWernerCascade

noncomputable section
open QuantumWernerCascade QuantumCascadeReduction QuantumMixedEnvironment
open QuantumCentralDepolarization QuantumNoisyVisibility QuantumRectangularSwapping
open QuantumEntanglementSwappingPurificationContract
open scoped BigOperators Matrix Kronecker ComplexOrder

def vOne : Visibility := ⟨1, by norm_num, by norm_num⟩
def vHalf : Visibility := ⟨1/2, by norm_num, by norm_num⟩

-- Three input pairs with visibility 1/2, with ideal gates: w_out=1/8, F_out=11/32.
example (σ₁ : EnvironmentState (Fin 2)) (σ₂ : EnvironmentState (Fin 3)) :
    (targetOverlap (acceptedCascade (wernerCascade vOne vOne vOne vOne vHalf σ₂)
      ((isotropic vHalf ⊗ₖ isotropic vHalf) ⊗ₖ σ₁.matrix))).re = 11/32 := by
  rw [cascade_fidelity_transition]
  norm_num [vOne, vHalf, ofVisibilities, alphaParam, wernerTransition, wernerFidelity]

-- Independent noise factors in the second round give w_out=1/32, F_out=35/128.
example (σ₁ : EnvironmentState (Fin 2)) (σ₂ : EnvironmentState (Fin 3)) :
    (targetOverlap (acceptedCascade (wernerCascade vOne vOne vHalf vHalf vHalf σ₂)
      ((isotropic vHalf ⊗ₖ isotropic vHalf) ⊗ₖ σ₁.matrix))).re = 35/128 := by
  rw [cascade_fidelity_transition]
  norm_num [vOne, vHalf, ofVisibilities, alphaParam, wernerTransition, wernerFidelity]

-- A full matrix equality, with the first and second memories of different dimensions.
example (σ₁ : EnvironmentState (Fin 2)) (σ₂ : EnvironmentState (Fin 3)) :
    acceptedCascade (wernerCascade vOne vOne vOne vOne vHalf σ₂)
      ((isotropic vHalf ⊗ₖ isotropic vHalf) ⊗ₖ σ₁.matrix) =
      isotropic ⟨1/8, by norm_num, by norm_num⟩ := by
  rw [cascade_visibility_matrix]
  congr 1
  norm_num [multiplyVisibility, vOne, vHalf]

example (σ₁ : EnvironmentState (Fin 2)) (σ₂ : EnvironmentState (Fin 3)) :
    (acceptedCascade (wernerCascade vOne vOne vHalf vHalf vHalf σ₂)
      ((isotropic vHalf ⊗ₖ isotropic vHalf) ⊗ₖ σ₁.matrix)).trace = 1 :=
  cascade_visibility_trace _ _ _ _ _ _ _ _ _
