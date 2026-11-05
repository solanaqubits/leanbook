/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumGeneralBellReadout
import Verification.QuantumNoisySwapping

/-! General classical readout and selective event loss on the ideal two-pair
swapping circuit. The accepted density is derived from actual circuit amplitudes.
Conditioning is available only at positive success mass. -/
noncomputable section
namespace QuantumSelectiveSwapping
open QuantumPauliMatrix QuantumPauliDensityBridge QuantumTwoQubitCPTP
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open QuantumBellCircuitRefinement QuantumNoisyBellInstrument
open QuantumNoisySwapping QuantumGeneralBellReadout
open scoped BigOperators ComplexOrder

def jointWeight (model : Readout) (a r : BellMeasurement) : ℝ :=
  circuitProbability a swappingInput * QuantumGeneralBellReadout.observationWeight model a (some r)

theorem joint_formula (model : Readout) (a r : BellMeasurement) :
    jointWeight model a r = model.detection a / 4 * model.confusion a r := by
  rw [jointWeight, circuit_born_probability, QuantumGeneralBellReadout.observationWeight]
  ring

theorem joint_nonnegative (model : Readout) (a r : BellMeasurement) :
    0 ≤ jointWeight model a r := by
  rw [joint_formula]
  exact mul_nonneg (div_nonneg (model.detection_nonneg a) (by norm_num))
    (model.confusion_nonneg a r)

def acceptedMass (model : Readout) : ℝ := ∑ a, ∑ r, jointWeight model a r

def lostMass (model : Readout) : ℝ := ∑ a, (1 - model.detection a) / 4

theorem accepted_mass_formula (model : Readout) :
    acceptedMass model = ∑ a, model.detection a / 4 := by
  simp [acceptedMass, joint_formula, ← Finset.mul_sum, model.confusion_sum]

theorem accepted_mass_nonnegative (model : Readout) : 0 ≤ acceptedMass model := by
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun r _ => joint_nonnegative model a r

theorem complete_event_mass (model : Readout) : acceptedMass model + lostMass model = 1 := by
  rw [accepted_mass_formula]
  simp only [lostMass, sum_bell]
  ring

theorem accepted_mass_le_one (model : Readout) : acceptedMass model ≤ 1 := by
  have h : 0 ≤ lostMass model := Finset.sum_nonneg fun a _ =>
    div_nonneg (sub_nonneg.mpr (model.detection_le_one a)) (by norm_num)
  linarith [complete_event_mass model]

/-- Output conditioned on the true Bell branch, averaged over reported labels. -/
def rowDensity (model : Readout) (a : BellMeasurement) : PairDensity :=
  ∑ r, model.confusion a r • correctedDensity a r

theorem row_positive (model : Readout) (a : BellMeasurement) :
    (rowDensity model a).PosSemidef :=
  Matrix.posSemidef_sum _ fun r _ =>
    (corrected_density_positive a r).smul (model.confusion_nonneg a r)

theorem row_trace (model : Readout) (a : BellMeasurement) : (rowDensity model a).trace = 1 := by
  simp only [rowDensity, Matrix.trace_sum, Matrix.trace_smul, corrected_density_trace]
  simpa using congrArg (fun x : ℝ => (x : ℂ)) (model.confusion_sum a)

theorem row_overlap (model : Readout) (a : BellMeasurement) :
    targetOverlap (rowDensity model a) = (model.confusion a a : ℂ) := by
  unfold rowDensity
  rw [sum_bell]
  cases a <;> simp [targetOverlap_add, targetOverlap_real_smul, miscorrection_overlap]

def acceptedDensity (model : Readout) : PairDensity :=
  ∑ a, ∑ r, jointWeight model a r • correctedDensity a r

theorem accepted_positive (model : Readout) : (acceptedDensity model).PosSemidef :=
  Matrix.posSemidef_sum _ fun a _ => Matrix.posSemidef_sum _ fun r _ =>
    (corrected_density_positive a r).smul (joint_nonnegative model a r)

theorem accepted_density_rows (model : Readout) :
    acceptedDensity model = ∑ a, (model.detection a / 4) • rowDensity model a := by
  simp only [acceptedDensity, rowDensity, Finset.smul_sum, smul_smul, joint_formula]

theorem accepted_trace (model : Readout) :
    (acceptedDensity model).trace = (acceptedMass model : ℂ) := by
  simp [acceptedDensity, acceptedMass, Matrix.trace_sum, Matrix.trace_smul,
    corrected_density_trace]

/-- Direct use of the unnormalized quantum circuit amplitudes. -/
def circuitAcceptedDensity (model : Readout) : PairDensity :=
  ∑ a, ∑ r, QuantumGeneralBellReadout.observationWeight model a (some r) •
    purePairDensity (correctOuter r (readoutBranch a swappingInput))

theorem circuit_density_sound (model : Readout) :
    circuitAcceptedDensity model = acceptedDensity model := by
  unfold circuitAcceptedDensity acceptedDensity
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  rw [raw_branch_density, smul_smul, jointWeight, circuit_born_probability, mul_comm]

/-- Joint probability of acceptance and a correct classical label. -/
def correctMass (model : Readout) : ℝ :=
  ∑ a, model.detection a / 4 * model.confusion a a

theorem correct_mass_bounds (model : Readout) :
    0 ≤ correctMass model ∧ correctMass model ≤ acceptedMass model := by
  constructor
  · exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (div_nonneg (model.detection_nonneg a) (by norm_num))
        (model.confusion_nonneg a a)
  · rw [accepted_mass_formula]
    exact Finset.sum_le_sum fun a _ => mul_le_of_le_one_right
      (div_nonneg (model.detection_nonneg a) (by norm_num)) (confusion_le_one model a a)

theorem accepted_overlap (model : Readout) :
    targetOverlap (acceptedDensity model) = (correctMass model : ℂ) := by
  rw [accepted_density_rows]
  simp [sum_bell, targetOverlap_add, targetOverlap_real_smul, row_overlap, correctMass]

/-- The proof argument excludes conditioning on a null event. -/
def conditionalState (model : Readout) (h : 0 < acceptedMass model) : PairState where
  matrix := (acceptedMass model)⁻¹ • acceptedDensity model
  positive := (accepted_positive model).smul (le_of_lt (inv_pos.mpr h))
  trace_one := by
    rw [Matrix.trace_smul, accepted_trace]
    simp [Complex.real_smul, ne_of_gt h]

theorem conditional_fidelity (model : Readout) (h : 0 < acceptedMass model) :
    targetOverlap (conditionalState model h).matrix =
      ((correctMass model / acceptedMass model : ℝ) : ℂ) := by
  change targetOverlap ((acceptedMass model)⁻¹ • acceptedDensity model) = _
  rw [targetOverlap_real_smul, accepted_overlap]
  push_cast
  ring

theorem conditional_fidelity_bounds (model : Readout) (h : 0 < acceptedMass model) :
    0 ≤ correctMass model / acceptedMass model ∧
    correctMass model / acceptedMass model ≤ 1 := by
  exact ⟨div_nonneg (correct_mass_bounds model).1 (le_of_lt h),
    (div_le_one h).mpr (correct_mass_bounds model).2⟩

/-- Constant corrected row densities are sufficient for invariance under selective loss. -/
theorem constant_rows_conditional (model : Readout) (ρ : PairDensity)
    (hrows : ∀ a, rowDensity model a = ρ) (h : 0 < acceptedMass model) :
    (conditionalState model h).matrix = ρ := by
  change (acceptedMass model)⁻¹ • acceptedDensity model = ρ
  rw [accepted_density_rows]
  simp_rw [hrows]
  rw [← Finset.sum_smul, ← accepted_mass_formula, smul_smul,
    inv_mul_cancel₀ (ne_of_gt h), one_smul]

/-- Symmetric confusion still has constant corrected rows even with selective losses. -/
theorem symmetric_confusion_rows (model : Readout) (old : ReadoutModel)
    (hc : model.confusion = QuantumNoisyBellInstrument.confusion old) (a : BellMeasurement) :
    rowDensity model a = labelMixture old := by
  simpa only [rowDensity, hc] using row_density_formula old a

theorem symmetric_confusion_loss_invariant (model : Readout) (old : ReadoutModel)
    (hc : model.confusion = QuantumNoisyBellInstrument.confusion old)
    (h : 0 < acceptedMass model) : (conditionalState model h).matrix = labelMixture old :=
  constant_rows_conditional model _ (symmetric_confusion_rows model old hc) h

theorem symmetric_joint (old : ReadoutModel) (a r : BellMeasurement) :
    jointWeight (ofSymmetric old) a r = QuantumNoisySwapping.jointWeight old a (some r) := by
  simp only [jointWeight, QuantumNoisySwapping.jointWeight, symmetric_weights]

theorem symmetric_mass (old : ReadoutModel) :
    acceptedMass (ofSymmetric old) = QuantumNoisySwapping.acceptedMass old := by
  simp only [acceptedMass, QuantumNoisySwapping.acceptedMass,
    QuantumNoisySwapping.reportedMass, symmetric_joint]
  exact Finset.sum_comm

theorem symmetric_density (old : ReadoutModel) :
    acceptedDensity (ofSymmetric old) = QuantumNoisySwapping.acceptedDensity old := by
  simp only [acceptedDensity, QuantumNoisySwapping.acceptedDensity, symmetric_joint]

theorem symmetric_conditional (old : ReadoutModel)
    (h : 0 < acceptedMass (ofSymmetric old)) (hold : 0 < probability old.detection) :
    (conditionalState (ofSymmetric old) h).matrix =
      (QuantumNoisySwapping.conditionalState old hold).matrix := by
  change (acceptedMass (ofSymmetric old))⁻¹ • acceptedDensity (ofSymmetric old) = _
  rw [symmetric_mass, symmetric_density]
  rfl

/-- A deliberately biased readout that always reports Φ+. Selection retains
only the true Φ+ branch when enabled; preparation and gates remain ideal. -/
def phiPlusIndicator : BellMeasurement → ℝ
  | .phiPlus => 1
  | _ => 0

def biasedReadout (selective : Bool) : Readout where
  detection := fun a => if selective then phiPlusIndicator a else 1
  detection_nonneg := by intro a; cases selective <;> cases a <;> norm_num [phiPlusIndicator]
  detection_le_one := by intro a; cases selective <;> cases a <;> norm_num [phiPlusIndicator]
  confusion := fun _ r => if r = .phiPlus then 1 else 0
  confusion_nonneg := by intro a r; split_ifs <;> norm_num
  confusion_sum := by intro a; simp

theorem biased_mass (selective : Bool) :
    acceptedMass (biasedReadout selective) = if selective then 1 / 4 else 1 := by
  rw [accepted_mass_formula, sum_bell]
  cases selective <;> norm_num [biasedReadout, phiPlusIndicator]

theorem biased_correct_mass (selective : Bool) : correctMass (biasedReadout selective) = 1 / 4 := by
  cases selective <;> norm_num [correctMass, sum_bell, biasedReadout, phiPlusIndicator]

theorem biased_positive (selective : Bool) : 0 < acceptedMass (biasedReadout selective) := by
  rw [biased_mass]
  cases selective <;> norm_num

/-- Selection can increase postselected fidelity without improving the
unconditional contribution. -/
theorem selection_bias_counterexample :
    targetOverlap (conditionalState (biasedReadout false) (biased_positive false)).matrix =
      (1 / 4 : ℂ) ∧
    targetOverlap (conditionalState (biasedReadout true) (biased_positive true)).matrix = 1 ∧
    acceptedMass (biasedReadout true) < acceptedMass (biasedReadout false) ∧
    correctMass (biasedReadout true) = correctMass (biasedReadout false) := by
  norm_num [conditional_fidelity, biased_mass, biased_correct_mass]

theorem zero_mass_iff (model : Readout) :
    acceptedMass model = 0 ↔ ∀ a, model.detection a = 0 := by
  rw [accepted_mass_formula]
  have h := Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ha : a ∈ Finset.univ) =>
      div_nonneg (model.detection_nonneg a) (by norm_num : (0 : ℝ) ≤ 4))
  simpa using h

theorem zero_mass_zero_density (model : Readout) (h : acceptedMass model = 0) :
    acceptedDensity model = 0 := by
  rw [accepted_density_rows]
  simp [(zero_mass_iff model).mp h]

/-- Exact scalar criterion; constant row density is a stronger sufficient condition. -/
theorem fidelity_eq_iff_balance (model : Readout) (h : 0 < acceptedMass model) (f : ℝ) :
    correctMass model / acceptedMass model = f ↔
      (∑ a, model.detection a / 4 * (model.confusion a a - f)) = 0 := by
  have balance : (∑ a, model.detection a / 4 * (model.confusion a a - f)) =
      correctMass model - f * acceptedMass model := by
    simp only [mul_sub, Finset.sum_sub_distrib, correctMass, accepted_mass_formula,
      ← Finset.sum_mul]
    ring
  rw [div_eq_iff (ne_of_gt h), balance]
  constructor <;> intro heq <;> linarith

theorem constant_accuracy_fidelity (model : Readout) (h : 0 < acceptedMass model) (f : ℝ)
    (hc : ∀ a, model.confusion a a = f) : correctMass model / acceptedMass model = f := by
  rw [fidelity_eq_iff_balance model h f]
  simp [hc]

structure QuantumSelectiveSwappingSuite : Prop where
  mass_complete : ∀ model, acceptedMass model + lostMass model = 1
  mass_bounds : ∀ model, 0 ≤ acceptedMass model ∧ acceptedMass model ≤ 1
  circuit_density : ∀ model, circuitAcceptedDensity model = acceptedDensity model
  density_trace : ∀ model, (acceptedDensity model).trace = (acceptedMass model : ℂ)
  fidelity : ∀ model (h : 0 < acceptedMass model),
    targetOverlap (conditionalState model h).matrix =
      ((correctMass model / acceptedMass model : ℝ) : ℂ)
  null_event : ∀ model, acceptedMass model = 0 → acceptedDensity model = 0
  symmetric_specialization : ∀ old,
    acceptedDensity (ofSymmetric old) = QuantumNoisySwapping.acceptedDensity old
  constant_rows : ∀ model ρ, (∀ a, rowDensity model a = ρ) →
    ∀ h : 0 < acceptedMass model, (conditionalState model h).matrix = ρ

theorem verification_suite : QuantumSelectiveSwappingSuite :=
  ⟨complete_event_mass, fun model => ⟨accepted_mass_nonnegative model,
    accepted_mass_le_one model⟩, circuit_density_sound, accepted_trace,
    conditional_fidelity, zero_mass_zero_density, symmetric_density, constant_rows_conditional⟩

end QuantumSelectiveSwapping
