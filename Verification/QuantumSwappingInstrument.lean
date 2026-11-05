/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumRectangularSwapping

/-! A linear accepted swapping instrument from 16×16 to 4×4 matrices.
Complete positivity is proved through an independently defined ancillary block
extension. State normalization is separate from the linear instrument. -/
noncomputable section
namespace QuantumSwappingInstrument
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellCircuitRefinement
open QuantumGeneralBellReadout QuantumBellDiagonalInputs QuantumRectangularSwapping
open scoped BigOperators ComplexOrder Kronecker Matrix

def weight (model : Readout) (m r : BellMeasurement) : ℝ :=
  model.detection m * model.confusion m r

theorem weight_nonnegative (model : Readout) (m r : BellMeasurement) : 0 ≤ weight model m r :=
  mul_nonneg (model.detection_nonneg m) (model.confusion_nonneg m r)

theorem weight_sum (model : Readout) (m : BellMeasurement) :
    ∑ r, weight model m r = model.detection m := by
  simp [weight, ← Finset.mul_sum, model.confusion_sum]

def kraus (model : Readout) (m r : BellMeasurement) : BranchMatrix :=
  (Real.sqrt (weight model m r) : ℂ) • branchOperator m r

/-- Complex-linear, including on non-Hermitian input matrices. -/
def acceptedMap (model : Readout) (M : FourDensity) : PairDensity :=
  ∑ m, ∑ r, weight model m r •
    (branchOperator m r * M * (branchOperator m r).conjTranspose)

theorem sqrt_sandwich (w : ℝ) (hw : 0 ≤ w) (L : BranchMatrix) (M : FourDensity) :
    ((Real.sqrt w : ℂ) • L) * M * ((Real.sqrt w : ℂ) • L).conjTranspose =
      w • (L * M * L.conjTranspose) := by
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt hw]
  rfl

theorem accepted_kraus (model : Readout) (M : FourDensity) :
    acceptedMap model M = ∑ m, ∑ r, kraus model m r * M * (kraus model m r).conjTranspose := by
  simp only [kraus, sqrt_sandwich _ (weight_nonnegative model _ _), acceptedMap]

theorem accepted_add (model : Readout) (M N : FourDensity) :
    acceptedMap model (M + N) = acceptedMap model M + acceptedMap model N := by
  simp [acceptedMap, Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]

theorem accepted_smul (model : Readout) (c : ℂ) (M : FourDensity) :
    acceptedMap model (c • M) = c • acceptedMap model M := by
  simp only [acceptedMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro r _
  exact smul_comm _ _ _

def acceptedLinear (model : Readout) : FourDensity →ₗ[ℂ] PairDensity where
  toFun := acceptedMap model
  map_add' := accepted_add model
  map_smul' := accepted_smul model

theorem accepted_sum {α : Type*} [Fintype α] (model : Readout) (M : α → FourDensity) :
    acceptedMap model (∑ a, M a) = ∑ a, acceptedMap model (M a) :=
  map_sum (acceptedLinear model) M Finset.univ

theorem accepted_real_smul (model : Readout) (c : ℝ) (M : FourDensity) :
    acceptedMap model (c • M) = c • acceptedMap model M := by
  simp only [acceptedMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro r _
  exact smul_comm _ _ _

/-- Equal input density matrices give equal outputs, even when prepared via
different finite ensembles. Positivity/normalization is not needed for this algebraic fact. -/
theorem ensemble_independent {α β : Type*} [Fintype α] [Fintype β]
    (model : Readout) (p : α → ℝ) (q : β → ℝ)
    (M : α → FourDensity) (N : β → FourDensity)
    (h : (∑ a, p a • M a) = ∑ b, q b • N b) :
    (∑ a, p a • acceptedMap model (M a)) = ∑ b, q b • acceptedMap model (N b) := by
  have heq := congrArg (acceptedMap model) h
  simpa only [accepted_sum, accepted_real_smul] using heq

/-- Independent block action of id_d ⊗ acceptedMap, with different input/output dimensions. -/
def extension (d : Nat) (model : Readout)
    (R : Matrix (Fin d × FourIndex) (Fin d × FourIndex) ℂ) :
    Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ := fun a b =>
  acceptedMap model (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2

theorem extension_kraus (d : Nat) (model : Readout)
    (R : Matrix (Fin d × FourIndex) (Fin d × FourIndex) ℂ) :
    extension d model R = ∑ m, ∑ r,
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ kraus model m r) * R *
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ kraus model m r).conjTranspose := by
  ext a b : 2
  change acceptedMap model (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2 = _
  rw [accepted_kraus]
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite (starRingEnd ℂ),
    mul_ite, Finset.sum_add_distrib]

theorem completely_positive (d : Nat) (model : Readout)
    (R : Matrix (Fin d × FourIndex) (Fin d × FourIndex) ℂ) (hR : R.PosSemidef) :
    (extension d model R).PosSemidef := by
  rw [extension_kraus]
  exact Matrix.posSemidef_sum _ fun _ _ => Matrix.posSemidef_sum _ fun _ _ =>
    hR.mul_mul_conjTranspose_same _

theorem accepted_positive (model : Readout) (M : FourDensity) (hM : M.PosSemidef) :
    (acceptedMap model M).PosSemidef := by
  rw [accepted_kraus]
  exact Matrix.posSemidef_sum _ fun _ _ => Matrix.posSemidef_sum _ fun _ _ =>
    hM.mul_mul_conjTranspose_same _

/-- Detection effect on the input system; it need not be a scalar multiple of identity. -/
def acceptanceEffect (model : Readout) : FourDensity :=
  ∑ m, model.detection m • centralProjector m

theorem kraus_effect (model : Readout) (m r : BellMeasurement) :
    (kraus model m r).conjTranspose * kraus model m r =
      weight model m r • centralProjector m := by
  simp only [kraus, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, branch_effect]
  rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt (weight_nonnegative model m r)]
  rfl

theorem effect_formula (model : Readout) :
    (∑ m, ∑ r, (kraus model m r).conjTranspose * kraus model m r) =
      acceptanceEffect model := by
  simp only [kraus_effect, ← Finset.sum_smul, weight_sum, acceptanceEffect]

theorem effect_positive (model : Readout) : (acceptanceEffect model).PosSemidef :=
  Matrix.posSemidef_sum _ fun m _ =>
    (central_projector_positive m).smul (model.detection_nonneg m)

/-- Loewner upper bound: I - effect is PSD, not an entrywise matrix inequality. -/
theorem effect_le_identity (model : Readout) : (1 - acceptanceEffect model).PosSemidef := by
  have hid : 1 - acceptanceEffect model =
      ∑ m, (1 - model.detection m) • centralProjector m := by
    simp [sub_smul, Finset.sum_sub_distrib, central_completeness, acceptanceEffect]
  rw [hid]
  exact Matrix.posSemidef_sum _ fun m _ =>
    (central_projector_positive m).smul (sub_nonneg.mpr (model.detection_le_one m))

theorem full_detection_effect (model : Readout) (h : ∀ m, model.detection m = 1) :
    acceptanceEffect model = 1 := by
  simp [acceptanceEffect, h, central_completeness]

theorem accepted_trace (model : Readout) (M : FourDensity) :
    (acceptedMap model M).trace = (acceptanceEffect model * M).trace := by
  have hs (m : BellMeasurement) : (∑ r, (weight model m r : ℂ)) =
      (model.detection m : ℂ) := by exact_mod_cast weight_sum model m
  simp [acceptedMap, acceptanceEffect, Matrix.trace_sum, Matrix.trace_smul,
    sandwich_trace, branch_effect, Matrix.sum_mul, ← Finset.sum_mul, hs]

/-- Lost registrations complete the trace budget. No correction is selected in this branch. -/
def lostMap (model : Readout) (M : FourDensity) : PairDensity :=
  ∑ m, (1 - model.detection m) • (reduction m * M * (reduction m).conjTranspose)

theorem lost_positive (model : Readout) (M : FourDensity) (hM : M.PosSemidef) :
    (lostMap model M).PosSemidef :=
  Matrix.posSemidef_sum _ fun m _ => (hM.mul_mul_conjTranspose_same _).smul
    (sub_nonneg.mpr (model.detection_le_one m))

theorem lost_trace (model : Readout) (M : FourDensity) :
    (lostMap model M).trace = ((1 - acceptanceEffect model) * M).trace := by
  have hid : (∑ m, (1 - model.detection m) • centralProjector m) =
      1 - acceptanceEffect model := by
    simp [sub_smul, Finset.sum_sub_distrib, central_completeness, acceptanceEffect]
  rw [← hid]
  simp [lostMap, Matrix.trace_sum, Matrix.trace_smul, sandwich_trace,
    reduction_effect, Matrix.sum_mul]

theorem trace_balance (model : Readout) (M : FourDensity) :
    (acceptedMap model M).trace + (lostMap model M).trace = M.trace := by
  rw [accepted_trace, lost_trace, ← Matrix.trace_add, ← Matrix.add_mul]
  simp

theorem trace_nonincreasing (model : Readout) (M : FourDensity) (hM : M.PosSemidef) :
    (acceptedMap model M).trace.re ≤ M.trace.re := by
  have ht := congrArg Complex.re (trace_balance model M)
  have hn := (Complex.nonneg_iff.mp (lost_positive model M hM).trace_nonneg).1
  simp only [Complex.add_re] at ht
  linarith

/-- Correct classical labels are not needed for trace preservation. -/
theorem trace_preserving_full_detection (model : Readout) (h : ∀ m, model.detection m = 1)
    (M : FourDensity) : (acceptedMap model M).trace = M.trace := by
  rw [accepted_trace, full_detection_effect model h, Matrix.one_mul]

structure FourState where
  matrix : FourDensity
  positive : matrix.PosSemidef
  trace_one : matrix.trace = 1

def acceptanceProbability (model : Readout) (ρ : FourState) : ℝ :=
  (acceptedMap model ρ.matrix).trace.re

theorem acceptance_bounds (model : Readout) (ρ : FourState) :
    0 ≤ acceptanceProbability model ρ ∧ acceptanceProbability model ρ ≤ 1 := by
  refine ⟨(Complex.nonneg_iff.mp (accepted_positive model ρ.matrix ρ.positive).trace_nonneg).1, ?_⟩
  simpa [acceptanceProbability, ρ.trace_one] using trace_nonincreasing model ρ.matrix ρ.positive

theorem trace_eq_probability (model : Readout) (ρ : FourState) :
    (acceptedMap model ρ.matrix).trace = (acceptanceProbability model ρ : ℂ) := by
  have him := (Complex.nonneg_iff.mp (accepted_positive model ρ.matrix ρ.positive).trace_nonneg).2
  apply Complex.ext
  · rfl
  · simpa using him.symm

def conditionalState (model : Readout) (ρ : FourState)
    (h : 0 < acceptanceProbability model ρ) : PairState where
  matrix := (acceptanceProbability model ρ)⁻¹ • acceptedMap model ρ.matrix
  positive := (accepted_positive model ρ.matrix ρ.positive).smul (le_of_lt (inv_pos.mpr h))
  trace_one := by
    rw [Matrix.trace_smul, trace_eq_probability]
    simp [Complex.real_smul, ne_of_gt h]

theorem product_component_refinement (model : Readout) (a b : BellMeasurement) :
    acceptedMap model (productDensity a b) =
      QuantumBellDiagonalSwapping.componentDensity model a b := by
  unfold acceptedMap QuantumBellDiagonalSwapping.componentDensity
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro r _
  rw [component_refinement, smul_smul]
  congr 1
  unfold weight
  ring

theorem bell_diagonal_refinement (model : Readout) (p q : BellDistribution) :
    acceptedMap model (inputDensity p q) =
      QuantumBellDiagonalSwapping.acceptedDensity p q model := by
  simp only [inputDensity, accepted_sum, accepted_real_smul, product_component_refinement,
    QuantumBellDiagonalSwapping.acceptedDensity]

def bellInputState (p q : BellDistribution) : FourState :=
  ⟨inputDensity p q, input_positive p q, input_trace p q⟩

theorem bell_diagonal_probability (model : Readout) (p q : BellDistribution) :
    acceptanceProbability model (bellInputState p q) =
      QuantumSelectiveSwapping.acceptedMass model := by
  unfold acceptanceProbability bellInputState
  rw [bell_diagonal_refinement, QuantumBellDiagonalSwapping.accepted_trace]
  simp

theorem bell_diagonal_conditional (model : Readout) (p q : BellDistribution)
    (h : 0 < acceptanceProbability model (bellInputState p q))
    (hold : 0 < QuantumSelectiveSwapping.acceptedMass model) :
    (conditionalState model (bellInputState p q) h).matrix =
      (QuantumBellDiagonalSwapping.conditionalState p q model hold).matrix := by
  change (acceptanceProbability model (bellInputState p q))⁻¹ •
    acceptedMap model (inputDensity p q) = _
  rw [bell_diagonal_probability, bell_diagonal_refinement]
  rfl

/-- Born probability before registration loss, for a general correlated input. -/
def bornProbability (m : BellMeasurement) (ρ : FourState) : ℝ :=
  (reduction m * ρ.matrix * (reduction m).conjTranspose).trace.re

theorem born_nonnegative (m : BellMeasurement) (ρ : FourState) :
    0 ≤ bornProbability m ρ :=
  (Complex.nonneg_iff.mp (ρ.positive.mul_mul_conjTranspose_same _).trace_nonneg).1

theorem born_total (ρ : FourState) : ∑ m, bornProbability m ρ = 1 := by
  have ht : (∑ m, (reduction m * ρ.matrix * (reduction m).conjTranspose).trace) = 1 := by
    simp only [sandwich_trace, reduction_effect, ← Matrix.trace_sum, ← Matrix.sum_mul,
      central_completeness, Matrix.one_mul, ρ.trace_one]
  simpa [bornProbability] using congrArg Complex.re ht

theorem acceptance_born_formula (model : Readout) (ρ : FourState) :
    acceptanceProbability model ρ = ∑ m, model.detection m * bornProbability m ρ := by
  simp [acceptanceProbability, accepted_trace, acceptanceEffect, Matrix.sum_mul,
    Matrix.trace_sum, Matrix.trace_smul, bornProbability, sandwich_trace, reduction_effect]

/-- A coherent GHZ input, not an independent Bell-diagonal pair ensemble. -/
def ghzKet : FourKet := fun a b c d =>
  if a = b ∧ b = c ∧ c = d then bellCoeff else 0

def ghzState : FourState where
  matrix := pureFourDensity ghzKet
  positive := Matrix.posSemidef_vecMulVec_self_star _
  trace_one := by
    norm_num [pureFourDensity, flattenFour, ghzKet, Matrix.trace, Matrix.diag,
      Matrix.vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_two, ← pow_two, bellCoeff_sq]

theorem ghz_born_probabilities (m : BellMeasurement) :
    bornProbability m ghzState =
      (match m with | .phiPlus | .phiMinus => 1 / 2 | .psiPlus | .psiMinus => 0) := by
  unfold bornProbability ghzState
  dsimp only
  rw [pureFourDensity, sandwich_pure, reduction_amplitudes]
  change (purePairDensity (readoutBranch m ghzKet)).trace.re = _
  rw [pure_pair_trace, branch_equals_bell_contraction]
  cases m <;> norm_num [pairNormSq, swappingContraction, ghzKet, bellKet,
    Fin.sum_univ_two, ← pow_two, bellCoeff_sq]

theorem ghz_acceptance_not_uniform_average :
    acceptanceProbability (QuantumSelectiveSwapping.biasedReadout true) ghzState = 1 / 2 ∧
    QuantumSelectiveSwapping.acceptedMass (QuantumSelectiveSwapping.biasedReadout true) =
      1 / 4 := by
  constructor
  · rw [acceptance_born_formula]
    norm_num [QuantumNoisyBellInstrument.sum_bell, QuantumSelectiveSwapping.biasedReadout,
      ghz_born_probabilities, QuantumSelectiveSwapping.phiPlusIndicator]
  · exact QuantumSelectiveSwapping.biased_mass true

structure QuantumSwappingInstrumentSuite : Prop where
  cp : ∀ d model R, R.PosSemidef → (extension d model R).PosSemidef
  trace_bound : ∀ model M, M.PosSemidef → (acceptedMap model M).trace.re ≤ M.trace.re
  full_detection : ∀ model, (∀ m, model.detection m = 1) →
    ∀ M, (acceptedMap model M).trace = M.trace
  bell_bridge : ∀ model p q, acceptedMap model (inputDensity p q) =
    QuantumBellDiagonalSwapping.acceptedDensity p q model
  born_normalized : ∀ ρ, ∑ m, bornProbability m ρ = 1
  probability_formula : ∀ model ρ,
    acceptanceProbability model ρ = ∑ m, model.detection m * bornProbability m ρ

theorem verification_suite : QuantumSwappingInstrumentSuite :=
  ⟨completely_positive, trace_nonincreasing, trace_preserving_full_detection,
    bell_diagonal_refinement, born_total, acceptance_born_formula⟩

end QuantumSwappingInstrument
