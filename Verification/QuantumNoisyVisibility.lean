/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCentralDepolarization

/-! Visibility multiplication for explicitly specified channels: central BC
isotropic depolarization, perfect readout, and output AD isotropic depolarization.
No universal fidelity-degradation claim is made for arbitrary CPTP maps. -/
noncomputable section
namespace QuantumNoisyVisibility
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGeneralBellReadout (Readout)
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization
open QuantumBellDiagonalSwapping (isotropicDistribution visibility_product_valid perfectReadout
  idealDensity uniformDistribution uniform_bell_sum uniform_input_erases_ideal_output
  isotropic_visibility_product density_overlap)
open QuantumNoisyBellInstrument (sum_bell)
open scoped BigOperators ComplexOrder Kronecker Matrix

theorem uniform_density : density uniformDistribution = maximallyMixed := by
  have hx (a : BellMeasurement) : bellXor a .phiPlus = a := by cases a <;> rfl
  simpa only [hx, density, uniformDistribution] using uniform_bell_sum .phiPlus

theorem fully_mixed_input :
    fullyMixedFour = inputDensity uniformDistribution uniformDistribution := by
  rw [input_density_tensor, uniform_density]
  ext i j : 2
  simp [fullyMixedFour, maximallyMixed, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all
  all_goals norm_num

theorem ideal_accepted (p q : BellDistribution) :
    acceptedMap perfectReadout (inputDensity p q) = idealDensity p q := by
  rw [bell_diagonal_refinement]
  simp only [QuantumBellDiagonalSwapping.acceptedDensity,
    QuantumBellDiagonalSwapping.perfect_component, idealDensity]

theorem fully_mixed_output : acceptedMap perfectReadout fullyMixedFour = maximallyMixed := by
  rw [fully_mixed_input, ideal_accepted, uniform_input_erases_ideal_output]

def multiplyVisibility (a b : Visibility) : Visibility :=
  ⟨a.val * b.val, (visibility_product_valid _ _ ⟨a.nonnegative,a.le_one⟩
    ⟨b.nonnegative,b.le_one⟩).1, (visibility_product_valid _ _ ⟨a.nonnegative,a.le_one⟩
    ⟨b.nonnegative,b.le_one⟩).2⟩

def isotropic (w : Visibility) : PairDensity :=
  density (isotropicDistribution w.val ⟨w.nonnegative,w.le_one⟩)

theorem isotropic_mix (g w : Visibility) :
    (g.val : ℂ) • isotropic w + ((1 - g.val : ℝ) : ℂ) • maximallyMixed =
      isotropic (multiplyVisibility g w) := by
  rw [← uniform_density]
  simp only [isotropic, density, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ext i j : 2
  cases a <;> simp [isotropicDistribution, uniformDistribution, multiplyVisibility,
    Matrix.smul_apply, Complex.real_smul] <;> ring

theorem isotropic_trace (w : Visibility) : (isotropic w).trace = 1 := density_trace _

theorem depolarizing_isotropic (g w : Visibility) :
    (depolarizing g).map (isotropic w) = isotropic (multiplyVisibility g w) := by
  rw [depolarizing_map, isotropic_trace, one_smul, ← isotropic_mix]
  congr 1
  ext i j : 2
  simp [maximallyMixed]
  ring

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

def noisyAccepted (pre : CPTP FourIndex κ) (post : BellMeasurement → CPTP PairIndex ι)
    (model : Readout) (M : FourDensity) : PairDensity :=
  ∑ r, noisyReported pre post model r M

theorem common_post_aggregate (pre : CPTP FourIndex κ) (post : CPTP PairIndex ι)
    (model : Readout) (M : FourDensity) :
    noisyAccepted pre (fun _ => post) model M = post.map (acceptedMap model (pre.map M)) := by
  rw [← reported_sum model (pre.map M)]
  simp only [noisyAccepted, noisyReported, noisyMicro, reportedMap, CPTP.map_sum]

def noisyWernerOutput (bsm corr w v : Visibility) : PairDensity :=
  noisyAccepted (centralChannel (depolarizing bsm)) (fun _ => depolarizing corr) perfectReadout
    (inputDensity (isotropicDistribution w.val ⟨w.nonnegative,w.le_one⟩)
      (isotropicDistribution v.val ⟨v.nonnegative,v.le_one⟩))

/-- Full matrix equality derived from central Kraus operators and the previous circuit bridge. -/
theorem noisy_visibility_matrix (bsm corr w v : Visibility) :
    noisyWernerOutput bsm corr w v =
      isotropic (multiplyVisibility corr (multiplyVisibility bsm (multiplyVisibility w v))) := by
  unfold noisyWernerOutput
  rw [common_post_aggregate, central_input_depolarization, accepted_add, accepted_smul,
    accepted_smul, ideal_accepted, fully_mixed_output, isotropic_visibility_product]
  change (depolarizing corr).map ((bsm.val : ℂ) • isotropic (multiplyVisibility w v) +
    ((1 - bsm.val : ℝ) : ℂ) • maximallyMixed) = _
  rw [isotropic_mix, depolarizing_isotropic]

theorem noisy_visibility_fidelity (bsm corr w v : Visibility) :
    targetOverlap (noisyWernerOutput bsm corr w v) =
      (((1 + 3 * corr.val * bsm.val * w.val * v.val) / 4 : ℝ) : ℂ) := by
  rw [noisy_visibility_matrix]
  simp [isotropic, density_overlap, isotropicDistribution, multiplyVisibility]
  ring

theorem noisy_visibility_trace (bsm corr w v : Visibility) :
    (noisyWernerOutput bsm corr w v).trace = 1 := by
  rw [noisy_visibility_matrix, isotropic_trace]

/-- On this isotropic family with g∈[0,1], target fidelity cannot increase. -/
theorem isotropic_fidelity_nonincreasing (g w : Visibility) :
    (targetOverlap ((depolarizing g).map (isotropic w))).re ≤ (targetOverlap (isotropic w)).re := by
  rw [depolarizing_isotropic]
  simp [isotropic, density_overlap, isotropicDistribution, multiplyVisibility]
  nlinarith [mul_nonneg (sub_nonneg.mpr g.le_one) w.nonnegative]

/-- A fixed unitary CPTP post-channel can improve a particular target fidelity. -/
def repairingPost : CPTP PairIndex Unit :=
  ⟨fun _ => correction .psiPlus, by simpa using correction_unitary .psiPlus⟩

theorem cptp_can_increase_target_fidelity :
    targetOverlap (QuantumNoisyBellInstrument.bellProjector .psiPlus) = 0 ∧
    targetOverlap (repairingPost.map (QuantumNoisyBellInstrument.bellProjector .psiPlus)) = 1 := by
  constructor
  · rw [QuantumBellDiagonalSwapping.projector_overlap,
      if_neg (show BellMeasurement.psiPlus ≠ .phiPlus from by decide)]
  · have hm : repairingPost.map (QuantumNoisyBellInstrument.bellProjector .psiPlus) =
        QuantumNoisySwapping.correctedDensity .psiPlus .psiPlus := by
      simp only [CPTP.map, repairingPost, Fintype.sum_unique,
        QuantumNoisyBellInstrument.bellProjector, purePairDensity, Matrix.mul_vecMulVec,
        Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
      change Matrix.vecMulVec (correction .psiPlus *ᵥ flattenPair (bellKet .psiPlus))
        (star (correction .psiPlus *ᵥ flattenPair (bellKet .psiPlus))) = _
      rw [correction_amplitudes, QuantumNoisySwapping.correctedDensity,
        QuantumNoisySwapping.correctedKet_eq]
      rfl
    rw [hm, QuantumNoisySwapping.miscorrection_overlap]
    simp

structure QuantumNoisyVisibilitySuite : Prop where
  matrix_formula : ∀ bsm corr w v,
    noisyWernerOutput bsm corr w v =
      isotropic (multiplyVisibility corr (multiplyVisibility bsm (multiplyVisibility w v)))
  fidelity_formula : ∀ bsm corr w v,
    targetOverlap (noisyWernerOutput bsm corr w v) =
      (((1 + 3 * corr.val * bsm.val * w.val * v.val) / 4 : ℝ) : ℂ)
  trace_one : ∀ bsm corr w v, (noisyWernerOutput bsm corr w v).trace = 1

theorem verification_suite : QuantumNoisyVisibilitySuite :=
  ⟨noisy_visibility_matrix, noisy_visibility_fidelity, noisy_visibility_trace⟩

end QuantumNoisyVisibility
