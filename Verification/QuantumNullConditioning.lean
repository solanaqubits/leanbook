/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumOutcomeInstrument
import Mathlib.Analysis.Matrix.PosDef

/-! Zero-probability branches, total conditional matrices and reconstruction.
Zero is a sentinel matrix for an impossible event, never a normalized quantum state. -/
noncomputable section
namespace QuantumNullConditioning
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGeneralBellReadout (Readout)
open QuantumSwappingInstrument QuantumOutcomeInstrument
open QuantumNoisyBellInstrument (sum_bell)
open scoped BigOperators ComplexOrder Matrix

/-- PSD supplies the missing imaginary part when probability is stored as a real trace. -/
theorem psd_trace_real (A : PairDensity) (hA : A.PosSemidef) :
    A.trace = (A.trace.re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm

theorem psd_zero_probability_iff (A : PairDensity) (hA : A.PosSemidef) :
    A.trace.re = 0 ↔ A = 0 := by
  constructor
  · intro h
    apply hA.trace_eq_zero_iff.mp
    rw [psd_trace_real A hA, h]
    rfl
  · intro h
    simp [h]

theorem micro_zero_iff (model : Readout) (m r : BellMeasurement) (ρ : FourState) :
    microProbability model m r ρ = 0 ↔ microMap model m r ρ.matrix = 0 :=
  psd_zero_probability_iff _ (micro_positive model m r ρ.matrix ρ.positive)

theorem outcome_zero_iff (model : Readout) (o : Outcome) (ρ : FourState) :
    outcomeProbability model o ρ = 0 ↔ outcomeMap model o ρ.matrix = 0 :=
  psd_zero_probability_iff _ (outcome_positive model o ρ.matrix ρ.positive)

/-- The zero branch is explicitly separated from density matrices of trace one. -/
def normalizeOrZero (A : PairDensity) : PairDensity :=
  if 0 < A.trace.re then A.trace.re⁻¹ • A else 0

theorem normalize_positive (A : PairDensity) (hA : A.PosSemidef) :
    (normalizeOrZero A).PosSemidef := by
  unfold normalizeOrZero
  split_ifs with h
  · exact hA.smul (le_of_lt (inv_pos.mpr h))
  · exact Matrix.PosSemidef.zero

theorem normalize_trace_one (A : PairDensity) (hA : A.PosSemidef) (h : 0 < A.trace.re) :
    (normalizeOrZero A).trace = 1 := by
  rw [normalizeOrZero, if_pos h, Matrix.trace_smul, psd_trace_real A hA]
  simp [Complex.real_smul, ne_of_gt h]

theorem normalize_null (A : PairDensity) (h : A.trace.re = 0) : normalizeOrZero A = 0 := by
  simp [normalizeOrZero, h]

theorem normalize_reconstruct (A : PairDensity) (hA : A.PosSemidef) :
    A.trace.re • normalizeOrZero A = A := by
  unfold normalizeOrZero
  split_ifs with h
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt h), one_smul]
  · have hn := (Complex.nonneg_iff.mp hA.trace_nonneg).1
    have hz : A.trace.re = 0 := by linarith
    rw [(psd_zero_probability_iff A hA).mp hz]
    simp

def microConditional (model : Readout) (m r : BellMeasurement) (ρ : FourState) : PairDensity :=
  normalizeOrZero (microMap model m r ρ.matrix)

def outcomeConditional (model : Readout) (o : Outcome) (ρ : FourState) : PairDensity :=
  normalizeOrZero (outcomeMap model o ρ.matrix)

def outcomeState (model : Readout) (o : Outcome) (ρ : FourState)
    (h : 0 < outcomeProbability model o ρ) : PairState where
  matrix := outcomeConditional model o ρ
  positive := normalize_positive _ (outcome_positive model o ρ.matrix ρ.positive)
  trace_one := normalize_trace_one _ (outcome_positive model o ρ.matrix ρ.positive) h

def microState (model : Readout) (m r : BellMeasurement) (ρ : FourState)
    (h : 0 < microProbability model m r ρ) : PairState where
  matrix := microConditional model m r ρ
  positive := normalize_positive _ (micro_positive model m r ρ.matrix ρ.positive)
  trace_one := normalize_trace_one _ (micro_positive model m r ρ.matrix ρ.positive) h

theorem micro_reconstruct (model : Readout) (m r : BellMeasurement) (ρ : FourState) :
    microProbability model m r ρ • microConditional model m r ρ =
      microMap model m r ρ.matrix :=
  normalize_reconstruct _ (micro_positive model m r ρ.matrix ρ.positive)

theorem outcome_reconstruct (model : Readout) (o : Outcome) (ρ : FourState) :
    outcomeProbability model o ρ • outcomeConditional model o ρ = outcomeMap model o ρ.matrix :=
  normalize_reconstruct _ (outcome_positive model o ρ.matrix ρ.positive)

theorem impossible_outcome (model : Readout) (o : Outcome) (ρ : FourState)
    (h : outcomeProbability model o ρ = 0) :
    outcomeMap model o ρ.matrix = 0 ∧ outcomeConditional model o ρ = 0 :=
  ⟨(outcome_zero_iff model o ρ).mp h, normalize_null _ h⟩

theorem reported_barycenter (model : Readout) (ρ : FourState) :
    (∑ r, outcomeProbability model (some r) ρ • outcomeConditional model (some r) ρ) =
      acceptedMap model ρ.matrix := by
  simp only [outcome_reconstruct]
  exact reported_sum model ρ.matrix

theorem positive_reported_barycenter (model : Readout) (ρ : FourState) :
    (∑ r ∈ Finset.univ.filter (fun r => 0 < outcomeProbability model (some r) ρ),
      outcomeProbability model (some r) ρ • outcomeConditional model (some r) ρ) =
      acceptedMap model ρ.matrix := by
  rw [Finset.sum_filter]
  rw [← reported_barycenter model ρ]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs with h
  · rfl
  · have hn := outcome_probability_nonnegative model (some r) ρ
    have hz : outcomeProbability model (some r) ρ = 0 := by linarith
    simp [hz]

def acceptedConditional (model : Readout) (ρ : FourState) : PairDensity :=
  normalizeOrZero (acceptedMap model ρ.matrix)

theorem accepted_reconstruct (model : Readout) (ρ : FourState) :
    acceptanceProbability model ρ • acceptedConditional model ρ = acceptedMap model ρ.matrix :=
  normalize_reconstruct _ (accepted_positive model ρ.matrix ρ.positive)

theorem conditional_v411_refinement (model : Readout) (ρ : FourState)
    (h : 0 < acceptanceProbability model ρ) :
    acceptedConditional model ρ = (conditionalState model ρ h).matrix := by
  unfold acceptedConditional normalizeOrZero
  change 0 < (acceptedMap model ρ.matrix).trace.re at h
  rw [if_pos h]
  rfl

theorem conditional_barycenter (model : Readout) (ρ : FourState)
    (h : 0 < acceptanceProbability model ρ) :
    (conditionalState model ρ h).matrix =
      ∑ r, (outcomeProbability model (some r) ρ / acceptanceProbability model ρ) •
        outcomeConditional model (some r) ρ := by
  change (acceptanceProbability model ρ)⁻¹ • acceptedMap model ρ.matrix = _
  rw [← reported_barycenter model ρ, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [smul_smul, div_eq_mul_inv, mul_comm]

theorem conditional_weights_total (model : Readout) (ρ : FourState)
    (h : 0 < acceptanceProbability model ρ) :
    (∑ r, outcomeProbability model (some r) ρ / acceptanceProbability model ρ) = 1 := by
  rw [← Finset.sum_div, reported_probability_sum, div_self (ne_of_gt h)]

theorem accepted_null_all_reports (model : Readout) (ρ : FourState)
    (h : acceptanceProbability model ρ = 0) :
    ∀ r, outcomeMap model (some r) ρ.matrix = 0 := by
  have hs : (∑ r, outcomeProbability model (some r) ρ) = 0 := by
    rw [reported_probability_sum, h]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r _ => outcome_probability_nonnegative model (some r) ρ)).mp hs
  intro r
  exact (outcome_zero_iff model (some r) ρ).mp (hz r (Finset.mem_univ r))

/-- A physical zero Born branch stays zero regardless of confusion labels. -/
theorem ghz_psi_micro_null (model : Readout) (r : BellMeasurement) :
    microMap model .psiPlus r ghzState.matrix = 0 := by
  apply (micro_zero_iff model .psiPlus r ghzState).mp
  rw [micro_probability_born, ghz_born_probabilities]
  simp

theorem ghz_ideal_report_null :
    outcomeMap QuantumBellDiagonalSwapping.perfectReadout (some .psiPlus) ghzState.matrix = 0 ∧
    outcomeConditional QuantumBellDiagonalSwapping.perfectReadout (some .psiPlus) ghzState = 0 := by
  apply impossible_outcome
  rw [reported_probability_born, sum_bell]
  norm_num [weight, QuantumBellDiagonalSwapping.perfectReadout, ghz_born_probabilities,
    show BellMeasurement.phiPlus ≠ .psiPlus from by decide,
    show BellMeasurement.phiMinus ≠ .psiPlus from by decide]

/-- All clicks are incorrectly reported as Ψ+; true BSM statistics are unchanged. -/
def alwaysPsiReadout : Readout where
  detection := fun _ => 1
  detection_nonneg := by intro m; norm_num
  detection_le_one := by intro m; norm_num
  confusion := fun _ r => if r = .psiPlus then 1 else 0
  confusion_nonneg := by intro m r; split_ifs <;> norm_num
  confusion_sum := by intro m; simp

theorem zero_true_branch_nonzero_report :
    bornProbability .psiPlus ghzState = 0 ∧
    outcomeProbability alwaysPsiReadout (some .psiPlus) ghzState = 1 := by
  constructor
  · exact ghz_born_probabilities .psiPlus
  · rw [reported_probability_born, sum_bell]
    norm_num [weight, alwaysPsiReadout, ghz_born_probabilities]

structure QuantumNullConditioningSuite : Prop where
  null_iff : ∀ model o ρ,
    outcomeProbability model o ρ = 0 ↔ outcomeMap model o ρ.matrix = 0
  microscopic_null_iff : ∀ model m r ρ,
    microProbability model m r ρ = 0 ↔ microMap model m r ρ.matrix = 0
  reconstruct : ∀ model o ρ,
    outcomeProbability model o ρ • outcomeConditional model o ρ = outcomeMap model o ρ.matrix
  barycenter : ∀ model ρ,
    (∑ r, outcomeProbability model (some r) ρ • outcomeConditional model (some r) ρ) =
      acceptedMap model ρ.matrix
  normalized_barycenter : ∀ model ρ (h : 0 < acceptanceProbability model ρ),
    (conditionalState model ρ h).matrix =
      ∑ r, (outcomeProbability model (some r) ρ / acceptanceProbability model ρ) •
        outcomeConditional model (some r) ρ

theorem verification_suite : QuantumNullConditioningSuite :=
  ⟨outcome_zero_iff, micro_zero_iff, outcome_reconstruct, reported_barycenter,
    conditional_barycenter⟩

end QuantumNullConditioning
