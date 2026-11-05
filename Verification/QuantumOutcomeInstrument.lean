/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumSwappingInstrument

/-! A finite instrument with four reported Bell labels and one rejection outcome.
Microscopic true labels remain hidden when classical readout is noisy. -/
noncomputable section
namespace QuantumOutcomeInstrument
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGeneralBellReadout QuantumSwappingInstrument
open scoped BigOperators ComplexOrder Kronecker Matrix

/-- Block action of id_d ⊗ Φ, defined independently of Kraus representations. -/
def liftMap (d : Nat) (Φ : FourDensity → PairDensity)
    (R : Matrix (Fin d × FourIndex) (Fin d × FourIndex) ℂ) :
    Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ := fun a b =>
  Φ (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2

def IsCP (Φ : FourDensity → PairDensity) : Prop :=
  ∀ d (R : Matrix (Fin d × FourIndex) (Fin d × FourIndex) ℂ),
    R.PosSemidef → (liftMap d Φ R).PosSemidef

def familyMap {α : Type*} [Fintype α] (K : α → BranchMatrix) (M : FourDensity) : PairDensity :=
  ∑ a, K a * M * (K a).conjTranspose

theorem lift_family {α : Type*} [Fintype α] (d : Nat) (K : α → BranchMatrix)
    (R : Matrix (Fin d × FourIndex) (Fin d × FourIndex) ℂ) :
    liftMap d (familyMap K) R = ∑ a,
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ K a) * R *
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ K a).conjTranspose := by
  ext a b : 2
  simp [liftMap, familyMap, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite (starRingEnd ℂ),
    mul_ite, Finset.sum_add_distrib]

theorem family_cp {α : Type*} [Fintype α] (K : α → BranchMatrix) : IsCP (familyMap K) := by
  intro d R hR
  rw [lift_family]
  exact Matrix.posSemidef_sum _ fun _ _ => hR.mul_mul_conjTranspose_same _

def microMap (model : Readout) (m r : BellMeasurement) (M : FourDensity) : PairDensity :=
  weight model m r • (branchOperator m r * M * (branchOperator m r).conjTranspose)

def reportedMap (model : Readout) (r : BellMeasurement) (M : FourDensity) : PairDensity :=
  ∑ m, microMap model m r M

def rejectKraus (model : Readout) (m : BellMeasurement) : BranchMatrix :=
  (Real.sqrt (1 - model.detection m) : ℂ) • reduction m

theorem micro_kraus (model : Readout) (m r : BellMeasurement) (M : FourDensity) :
    microMap model m r M = kraus model m r * M * (kraus model m r).conjTranspose := by
  rw [kraus, sqrt_sandwich _ (weight_nonnegative model m r)]
  rfl

theorem reported_family (model : Readout) (r : BellMeasurement) :
    reportedMap model r = familyMap (fun m => kraus model m r) := by
  funext M
  simp only [reportedMap, micro_kraus, familyMap]

theorem reject_family (model : Readout) : lostMap model = familyMap (rejectKraus model) := by
  funext M
  simp only [familyMap, rejectKraus,
    sqrt_sandwich _ (sub_nonneg.mpr (model.detection_le_one _)), lostMap]

theorem micro_cp (model : Readout) (m r : BellMeasurement) : IsCP (microMap model m r) := by
  have h : microMap model m r = familyMap (fun _ : Unit => kraus model m r) := by
    funext M
    simp [familyMap, micro_kraus]
  rw [h]
  exact family_cp _

theorem reported_cp (model : Readout) (r : BellMeasurement) : IsCP (reportedMap model r) := by
  rw [reported_family]
  exact family_cp _

theorem reject_cp (model : Readout) : IsCP (lostMap model) := by
  rw [reject_family]
  exact family_cp _

theorem micro_positive (model : Readout) (m r : BellMeasurement)
    (M : FourDensity) (hM : M.PosSemidef) : (microMap model m r M).PosSemidef := by
  rw [micro_kraus]
  exact hM.mul_mul_conjTranspose_same _

theorem reported_positive (model : Readout) (r : BellMeasurement)
    (M : FourDensity) (hM : M.PosSemidef) : (reportedMap model r M).PosSemidef :=
  Matrix.posSemidef_sum _ fun m _ => micro_positive model m r M hM

theorem reported_sum (model : Readout) (M : FourDensity) :
    (∑ r, reportedMap model r M) = acceptedMap model M := by
  exact Finset.sum_comm

/-- none is rejection; some r is a delivered classical label. -/
abbrev Outcome := Option BellMeasurement

def outcomeMap (model : Readout) : Outcome → FourDensity → PairDensity
  | none => lostMap model
  | some r => reportedMap model r

theorem outcome_cp (model : Readout) (o : Outcome) : IsCP (outcomeMap model o) := by
  cases o with
  | none => exact reject_cp model
  | some r => exact reported_cp model r

theorem outcome_positive (model : Readout) (o : Outcome) (M : FourDensity) (hM : M.PosSemidef) :
    (outcomeMap model o M).PosSemidef := by
  cases o with
  | none => exact lost_positive model M hM
  | some r => exact reported_positive model r M hM

theorem outcome_add (model : Readout) (o : Outcome) (M N : FourDensity) :
    outcomeMap model o (M + N) = outcomeMap model o M + outcomeMap model o N := by
  cases o <;> simp [outcomeMap, lostMap, reportedMap, microMap,
    Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]

theorem outcome_smul (model : Readout) (o : Outcome) (c : ℂ) (M : FourDensity) :
    outcomeMap model o (c • M) = c • outcomeMap model o M := by
  cases o <;> simp only [outcomeMap, lostMap, reportedMap, microMap,
    Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  all_goals
    apply Finset.sum_congr rfl
    intro m _
    exact smul_comm _ _ _

def outcomeLinear (model : Readout) (o : Outcome) : FourDensity →ₗ[ℂ] PairDensity where
  toFun := outcomeMap model o
  map_add' := outcome_add model o
  map_smul' := outcome_smul model o

theorem outcome_total (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, outcomeMap model o M) = lostMap model M + acceptedMap model M := by
  rw [Fintype.sum_option]
  change lostMap model M + (∑ r, reportedMap model r M) = _
  rw [reported_sum]

theorem outcome_total_trace (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, outcomeMap model o M).trace = M.trace := by
  rw [outcome_total, Matrix.trace_add, add_comm, trace_balance]

theorem outcome_trace_nonincreasing (model : Readout) (o : Outcome)
    (M : FourDensity) (hM : M.PosSemidef) : (outcomeMap model o M).trace.re ≤ M.trace.re := by
  have htotal := congrArg Complex.re (outcome_total_trace model M)
  rw [Matrix.trace_sum, Complex.re_sum] at htotal
  rw [← htotal]
  exact Finset.single_le_sum (fun i _ =>
    (Complex.nonneg_iff.mp (outcome_positive model i M hM).trace_nonneg).1) (Finset.mem_univ o)

theorem full_detection_no_reject (model : Readout) (h : ∀ m, model.detection m = 1)
    (M : FourDensity) : outcomeMap model none M = 0 := by
  simp [outcomeMap, lostMap, h]

def outcomeProbability (model : Readout) (o : Outcome) (ρ : FourState) : ℝ :=
  (outcomeMap model o ρ.matrix).trace.re

def microProbability (model : Readout) (m r : BellMeasurement) (ρ : FourState) : ℝ :=
  (microMap model m r ρ.matrix).trace.re

theorem outcome_probability_nonnegative (model : Readout) (o : Outcome) (ρ : FourState) :
    0 ≤ outcomeProbability model o ρ :=
  (Complex.nonneg_iff.mp (outcome_positive model o ρ.matrix ρ.positive).trace_nonneg).1

theorem outcome_probability_total (model : Readout) (ρ : FourState) :
    ∑ o : Outcome, outcomeProbability model o ρ = 1 := by
  have h := congrArg Complex.re (outcome_total_trace model ρ.matrix)
  simpa [Matrix.trace_sum, ρ.trace_one, outcomeProbability] using h

theorem outcome_probability_le_one (model : Readout) (o : Outcome) (ρ : FourState) :
    outcomeProbability model o ρ ≤ 1 := by
  rw [← outcome_probability_total model ρ]
  exact Finset.single_le_sum (fun i _ => outcome_probability_nonnegative model i ρ)
    (Finset.mem_univ o)

theorem reported_probability_sum (model : Readout) (ρ : FourState) :
    (∑ r, outcomeProbability model (some r) ρ) = acceptanceProbability model ρ := by
  have h := congrArg (fun M : PairDensity => M.trace.re) (reported_sum model ρ.matrix)
  simpa [outcomeProbability, outcomeMap, acceptanceProbability, Matrix.trace_sum] using h

theorem reject_probability (model : Readout) (ρ : FourState) :
    outcomeProbability model none ρ = 1 - acceptanceProbability model ρ := by
  have h := outcome_probability_total model ρ
  rw [Fintype.sum_option, reported_probability_sum] at h
  linarith

theorem micro_probability_born (model : Readout) (m r : BellMeasurement) (ρ : FourState) :
    microProbability model m r ρ = weight model m r * bornProbability m ρ := by
  simp [microProbability, microMap, Matrix.trace_smul, sandwich_trace, branch_effect,
    bornProbability, reduction_effect]

theorem reported_probability_born (model : Readout) (r : BellMeasurement) (ρ : FourState) :
    outcomeProbability model (some r) ρ = ∑ m, weight model m r * bornProbability m ρ := by
  simp only [outcomeProbability, outcomeMap, reportedMap, Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun m _ => micro_probability_born model m r ρ

structure QuantumOutcomeInstrumentSuite : Prop where
  microscopic_cp : ∀ model m r, IsCP (microMap model m r)
  reported_cp : ∀ model r, IsCP (reportedMap model r)
  reject_cp : ∀ model, IsCP (lostMap model)
  coarse_graining : ∀ model M, (∑ r, reportedMap model r M) = acceptedMap model M
  normalized_instrument : ∀ model M, (∑ o : Outcome, outcomeMap model o M).trace = M.trace
  normalized_probabilities : ∀ model ρ, ∑ o : Outcome, outcomeProbability model o ρ = 1

theorem verification_suite : QuantumOutcomeInstrumentSuite :=
  ⟨micro_cp, reported_cp, reject_cp, reported_sum, outcome_total_trace,
    outcome_probability_total⟩

end QuantumOutcomeInstrument
