/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumLocalPostNoise

/-! D-only post-noise refines the pair-noise visibility law on Bell-diagonal inputs.
The agreement is not extended to arbitrary inputs: a product-state counterexample
and a general marginal criterion delimit the contract. -/
noncomputable section
namespace QuantumLocalNoisySwapping
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGateNoiseComposition QuantumCentralDepolarization QuantumNoisyVisibility
open QuantumLocalPostNoise QuantumSwappingInstrument
open QuantumBellDiagonalSwapping (isotropicDistribution perfectReadout isotropic_visibility_product)
open QuantumNoisyBellInstrument (bellProjector)
open scoped BigOperators ComplexOrder Kronecker Matrix

theorem traceD_sum {α : Type*} [Fintype α] (M : α → PairDensity) :
    traceD (∑ a, M a) = ∑ a, traceD (M a) := by
  ext i j : 2
  simp only [traceD, Matrix.sum_apply]
  exact Finset.sum_comm

theorem traceD_smul (c : ℂ) (M : PairDensity) :
    traceD (c • M) = c • traceD M := by
  ext i j : 2
  simp [traceD, mul_add]

theorem traceD_bell (a : BellMeasurement) :
    traceD (bellProjector a) = (1 / 2 : ℂ) • (1 : QubitMatrix) := by
  ext i j : 2
  change (∑ d, bellKet a i d * star (bellKet a j d)) = _
  rw [bell_left_marginal]
  simp [Matrix.one_apply]

/-- Arbitrary complex Bell-projector combinations, not only normalized mixtures. -/
theorem bell_mixture_marginal (c : BellMeasurement → ℂ) :
    traceD (∑ a, c a • bellProjector a) =
      ((∑ a, c a • bellProjector a).trace / 2) • (1 : QubitMatrix) := by
  have ht (a : BellMeasurement) : (bellProjector a).trace = 1 := by
    rw [bellProjector, pure_pair_trace, bell_pair_normalized, Complex.ofReal_one]
  rw [traceD_sum]
  simp only [traceD_smul, traceD_bell, smul_smul, Matrix.trace_sum, Matrix.trace_smul,
    ht, smul_eq_mul, mul_one]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Finset.sum_mul]
  ring

theorem local_equals_pair_on_bell_mixture (g : Visibility) (c : BellMeasurement → ℂ) :
    (localDepolarizing g).map (∑ a, c a • bellProjector a) =
      (depolarizing g).map (∑ a, c a • bellProjector a) :=
  local_equals_pair_of_marginal g _ (bell_mixture_marginal c)

theorem local_equals_pair_on_density (g : Visibility) (p : BellDistribution) :
    (localDepolarizing g).map (density p) = (depolarizing g).map (density p) := by
  have h := local_equals_pair_on_bell_mixture g (fun a => (p.weight a : ℂ))
  simpa only [density, Complex.coe_smul] using h

theorem local_depolarizing_isotropic (g w : Visibility) :
    (localDepolarizing g).map (isotropic w) = isotropic (multiplyVisibility g w) := by
  rw [isotropic, local_equals_pair_on_density]
  exact depolarizing_isotropic g w

def localNoisyWernerOutput (bsm corr w v : Visibility) : PairDensity :=
  noisyAccepted (centralChannel (depolarizing bsm)) (fun _ => localDepolarizing corr)
    perfectReadout (inputDensity (isotropicDistribution w.val ⟨w.nonnegative,w.le_one⟩)
      (isotropicDistribution v.val ⟨v.nonnegative,v.le_one⟩))

theorem local_noisy_visibility_matrix (bsm corr w v : Visibility) :
    localNoisyWernerOutput bsm corr w v =
      isotropic (multiplyVisibility corr (multiplyVisibility bsm (multiplyVisibility w v))) := by
  unfold localNoisyWernerOutput
  rw [common_post_aggregate, central_input_depolarization, accepted_add, accepted_smul,
    accepted_smul, ideal_accepted, fully_mixed_output, isotropic_visibility_product]
  change (localDepolarizing corr).map ((bsm.val : ℂ) • isotropic (multiplyVisibility w v) +
    ((1 - bsm.val : ℝ) : ℂ) • maximallyMixed) = _
  rw [isotropic_mix, local_depolarizing_isotropic]

theorem local_noisy_refines_pair_model (bsm corr w v : Visibility) :
    localNoisyWernerOutput bsm corr w v = noisyWernerOutput bsm corr w v := by
  rw [local_noisy_visibility_matrix, noisy_visibility_matrix]

theorem local_noisy_visibility_fidelity (bsm corr w v : Visibility) :
    targetOverlap (localNoisyWernerOutput bsm corr w v) =
      (((1 + 3 * corr.val * bsm.val * w.val * v.val) / 4 : ℝ) : ℂ) := by
  rw [local_noisy_refines_pair_model, noisy_visibility_fidelity]

theorem local_noisy_visibility_trace (bsm corr w v : Visibility) :
    (localNoisyWernerOutput bsm corr w v).trace = 1 := by
  rw [local_noisy_refines_pair_model, noisy_visibility_trace]

theorem local_noisy_visibility_positive (bsm corr w v : Visibility) :
    (localNoisyWernerOutput bsm corr w v).PosSemidef := by
  rw [local_noisy_visibility_matrix]
  exact density_positive _

/-- A normalized product input with a nonmaximally mixed A marginal. -/
def productZero : PairDensity := Matrix.diagonal fun i => if i = (0,0) then 1 else 0

theorem product_zero_positive : productZero.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  change 0 ≤ if i = (0,0) then (1 : ℂ) else 0
  split_ifs <;> positivity

theorem product_zero_trace : productZero.trace = 1 := by
  simp [productZero, Matrix.trace, Matrix.diag]

theorem product_zero_marginal_not_mixed :
    traceD productZero ≠ (productZero.trace / 2) • (1 : QubitMatrix) := by
  intro h
  have he := congrArg (fun M : QubitMatrix => M 0 0) h
  rw [product_zero_trace] at he
  norm_num [traceD, productZero, Matrix.diagonal, Fin.sum_univ_two] at he

theorem local_and_pair_noise_differ_on_product (g : Visibility) (hg : g.val < 1) :
    (localDepolarizing g).map productZero ≠ (depolarizing g).map productZero := by
  intro h
  exact product_zero_marginal_not_mixed ((local_equals_pair_iff g hg productZero).mp h)

/-- At γ=1 the marginal restriction is unnecessary; both channels are identity. -/
theorem identity_endpoint_agrees (g : Visibility) (hg : g.val = 1) (M : PairDensity) :
    (localDepolarizing g).map M = M ∧ (depolarizing g).map M = M := by
  rw [local_depolarizing_formula, depolarizing_map, hg]
  simp

structure QuantumLocalNoisySwappingSuite : Prop where
  refinement : ∀ bsm corr w v,
    localNoisyWernerOutput bsm corr w v = noisyWernerOutput bsm corr w v
  fidelity : ∀ bsm corr w v,
    targetOverlap (localNoisyWernerOutput bsm corr w v) =
      (((1 + 3 * corr.val * bsm.val * w.val * v.val) / 4 : ℝ) : ℂ)
  product_boundary : ∀ g, g.val < 1 →
    (localDepolarizing g).map productZero ≠ (depolarizing g).map productZero

theorem verification_suite : QuantumLocalNoisySwappingSuite :=
  ⟨local_noisy_refines_pair_model, local_noisy_visibility_fidelity,
    local_and_pair_noise_differ_on_product⟩

end QuantumLocalNoisySwapping
