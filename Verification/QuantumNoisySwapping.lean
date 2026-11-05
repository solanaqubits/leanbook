/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoisyBellInstrument

/-! Noisy classical labels after ideal swapping. All formulas are derived from
Born weights and the actual correction selected by the reported label. Detection
is outcome-independent and misreporting is symmetric; conditioning requires a
strictly positive detection probability. -/
noncomputable section
namespace QuantumNoisySwapping
open QuantumPauliMatrix QuantumPauliDensityBridge QuantumTwoQubitCPTP
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open QuantumBellCircuitRefinement QuantumNoisyBellInstrument
open scoped BigOperators ComplexOrder

def jointWeight (model : ReadoutModel) (actual : BellMeasurement)
    (observed : Option BellMeasurement) : ℝ :=
  circuitProbability actual swappingInput * observationWeight model actual observed

def reportedMass (model : ReadoutModel) (r : BellMeasurement) : ℝ :=
  ∑ a, jointWeight model a (some r)

def acceptedMass (model : ReadoutModel) : ℝ := ∑ r, reportedMass model r

def lostMass (model : ReadoutModel) : ℝ := ∑ a, jointWeight model a none

theorem joint_nonnegative (model : ReadoutModel) (a : BellMeasurement)
    (o : Option BellMeasurement) : 0 ≤ jointWeight model a o := by
  rw [jointWeight, circuit_born_probability]
  exact mul_nonneg (by norm_num) (observation_nonnegative model a o)

theorem reported_mass_formula (model : ReadoutModel) (r : BellMeasurement) :
    reportedMass model r = probability model.detection / 4 := by
  unfold reportedMass
  rw [sum_bell]
  cases r <;> simp [jointWeight, circuit_born_probability, observationWeight, confusion] <;> ring

theorem accepted_mass_formula (model : ReadoutModel) :
    acceptedMass model = probability model.detection := by
  unfold acceptedMass
  rw [sum_bell]
  simp only [reported_mass_formula]
  ring

theorem lost_mass_formula (model : ReadoutModel) :
    lostMass model = 1 - probability model.detection := by
  unfold lostMass
  rw [sum_bell]
  simp only [jointWeight, circuit_born_probability, observationWeight]
  ring

theorem complete_event_mass (model : ReadoutModel) : acceptedMass model + lostMass model = 1 := by
  rw [accepted_mass_formula, lost_mass_formula]
  ring

/-- Feed-forward uses the reported label, not the unavailable true outcome. -/
def correctedKet (actual reported : BellMeasurement) : PairKet :=
  correctOuter reported ((2 : ℂ) • readoutBranch actual swappingInput)

theorem correctedKet_eq (a r : BellMeasurement) :
    correctedKet a r = correctOuter r (bellKet a) := by
  unfold correctedKet
  rw [branch_equals_bell_contraction]
  change correctOuter r (swappedOuter a) = _
  rw [swapped_outer_eq_bell]

def correctedDensity (a r : BellMeasurement) : PairDensity := purePairDensity (correctedKet a r)

theorem corrected_density_positive (a r : BellMeasurement) :
    (correctedDensity a r).PosSemidef := pure_pair_positive _

theorem corrected_density_trace (a r : BellMeasurement) : (correctedDensity a r).trace = 1 := by
  rw [correctedDensity, pure_pair_trace, correctedKet_eq]
  cases a <;> cases r <;>
    norm_num [pairNormSq, correctOuter, amp, applyCorrection, bellKet, Fin.sum_univ_two]

theorem miscorrection_overlap (a r : BellMeasurement) :
    targetOverlap (correctedDensity a r) = if a = r then 1 else 0 := by
  unfold correctedDensity
  rw [correctedKet_eq]
  cases a <;> cases r <;>
    simp [targetOverlap, purePairDensity, Matrix.vecMulVec, correctOuter, amp,
      applyCorrection, bellKet, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [bellCoeff_sq, bellCoeff_four]

/-- Closed Bell-diagonal expression, proved below from the branch mixture. -/
def labelMixture (model : ReadoutModel) : PairDensity :=
  (1 - probability model.corruption) • bellProjector .phiPlus +
    (probability model.corruption / 3) •
      (bellProjector .phiMinus + bellProjector .psiPlus + bellProjector .psiMinus)

set_option maxHeartbeats 2000000 in
-- Entrywise expansion checks 4 actual labels and all 16 matrix entries.
theorem row_density_formula (model : ReadoutModel) (a : BellMeasurement) :
    (∑ r, confusion model a r • correctedDensity a r) = labelMixture model := by
  rw [sum_bell]
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  cases a <;> fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    simp [confusion, correctedDensity, correctedKet_eq, labelMixture, bellProjector,
      purePairDensity, Matrix.vecMulVec, correctOuter, amp, applyCorrection,
      bellKet, Complex.real_smul] <;> ring

theorem bell_projector_trace (a : BellMeasurement) : (bellProjector a).trace = 1 := by
  rw [bellProjector, pure_pair_trace, bell_pair_normalized]
  rfl

theorem labelMixture_positive (model : ReadoutModel) : (labelMixture model).PosSemidef := by
  exact ((pure_pair_positive _).smul (sub_nonneg.mpr (probability_bounds _).2)).add
    (((pure_pair_positive _).add (pure_pair_positive _) |>.add (pure_pair_positive _)).smul
      (div_nonneg (probability_bounds _).1 (by norm_num)))

theorem labelMixture_trace (model : ReadoutModel) : (labelMixture model).trace = 1 := by
  simp [labelMixture, Matrix.trace_add, Matrix.trace_smul, bell_projector_trace]
  ring

theorem labelMixture_overlap (model : ReadoutModel) :
    targetOverlap (labelMixture model) = 1 - (probability model.corruption : ℂ) := by
  rw [← row_density_formula model .phiPlus, sum_bell]
  simp [targetOverlap_add, targetOverlap_real_smul, miscorrection_overlap, confusion]

/-- Sum of joint observed branches, before postselection normalization. -/
def acceptedDensity (model : ReadoutModel) : PairDensity :=
  ∑ a, ∑ r, jointWeight model a (some r) • correctedDensity a r

theorem accepted_density_formula (model : ReadoutModel) :
    acceptedDensity model = probability model.detection • labelMixture model := by
  have branch (a r : BellMeasurement) :
      jointWeight model a (some r) • correctedDensity a r =
      (probability model.detection / 4) • (confusion model a r • correctedDensity a r) := by
    simp only [jointWeight, circuit_born_probability, observationWeight, smul_smul]
    congr 1
    ring
  calc
    acceptedDensity model = ∑ a, (probability model.detection / 4) • labelMixture model := by
      unfold acceptedDensity
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [branch]
      rw [← Finset.smul_sum, row_density_formula]
    _ = _ := by
      rw [sum_bell]
      simp only [← add_smul]
      congr 1
      ring

theorem accepted_density_trace (model : ReadoutModel) :
    (acceptedDensity model).trace = (acceptedMass model : ℂ) := by
  rw [accepted_density_formula, Matrix.trace_smul, labelMixture_trace, accepted_mass_formula]
  simp

theorem normalized_accepted_eq (model : ReadoutModel)
    (hdet : 0 < probability model.detection) :
    (acceptedMass model)⁻¹ • acceptedDensity model = labelMixture model := by
  rw [accepted_density_formula, accepted_mass_formula, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hdet), one_smul]

/-- A physical conditional state is available only when the event has positive mass. -/
def conditionalState (model : ReadoutModel) (hdet : 0 < probability model.detection) : PairState :=
  { matrix := (acceptedMass model)⁻¹ • acceptedDensity model
    positive := by rw [normalized_accepted_eq model hdet]; exact labelMixture_positive model
    trace_one := by rw [normalized_accepted_eq model hdet]; exact labelMixture_trace model }

theorem conditional_matrix (model : ReadoutModel) (hdet : 0 < probability model.detection) :
    (conditionalState model hdet).matrix = labelMixture model :=
  normalized_accepted_eq model hdet

theorem conditional_fidelity (model : ReadoutModel) (hdet : 0 < probability model.detection) :
    targetOverlap (conditionalState model hdet).matrix =
      1 - (probability model.corruption : ℂ) := by
  rw [conditional_matrix, labelMixture_overlap]

theorem success_weighted_overlap (model : ReadoutModel) :
    targetOverlap (acceptedDensity model) =
      (probability model.detection : ℂ) * (1 - (probability model.corruption : ℂ)) := by
  rw [accepted_density_formula, targetOverlap_real_smul, labelMixture_overlap]

theorem conditional_after_depolarization (model : ReadoutModel)
    (hdet : 0 < probability model.detection) (p : BoundedBps) :
    targetOverlap (linearChannel p (conditionalState model hdet).matrix) =
      (1 - (probability p : ℂ)) * (1 - (probability model.corruption : ℂ)) +
        (probability p : ℂ) / 4 := by
  rw [state_map_agrees, depolarize_overlap, conditional_fidelity]

theorem no_detection_no_success (model : ReadoutModel) (hzero : model.detection.val = 0) :
    acceptedMass model = 0 ∧ acceptedDensity model = 0 := by
  simp [accepted_mass_formula, accepted_density_formula, probability, hzero]

theorem detection_does_not_change_conditional (m₁ m₂ : ReadoutModel)
    (h₁ : 0 < probability m₁.detection) (h₂ : 0 < probability m₂.detection)
    (hc : m₁.corruption = m₂.corruption) :
    (conditionalState m₁ h₁).matrix = (conditionalState m₂ h₂).matrix := by
  simp only [conditional_matrix, labelMixture, hc]

theorem correctOuter_double (r : BellMeasurement) (v : PairKet) :
    correctOuter r ((2 : ℂ) • v) = (2 : ℂ) • correctOuter r v := by
  funext a d
  cases r <;> fin_cases d <;> simp [correctOuter, amp, applyCorrection]

theorem pure_pair_double (v : PairKet) :
    purePairDensity ((2 : ℂ) • v) = (4 : ℝ) • purePairDensity v := by
  ext i j : 2
  simp [purePairDensity, Matrix.vecMulVec, Complex.real_smul]
  ring

theorem raw_branch_density (a r : BellMeasurement) :
    purePairDensity (correctOuter r (readoutBranch a swappingInput)) =
      (1 / 4 : ℝ) • correctedDensity a r := by
  unfold correctedDensity correctedKet
  rw [correctOuter_double, pure_pair_double, smul_smul]
  norm_num

/-- Direct subnormalized density sum of the actual circuit branches. -/
def circuitAcceptedDensity (model : ReadoutModel) : PairDensity :=
  ∑ a, ∑ r, observationWeight model a (some r) •
    purePairDensity (correctOuter r (readoutBranch a swappingInput))

theorem circuit_accepted_density_sound (model : ReadoutModel) :
    circuitAcceptedDensity model = acceptedDensity model := by
  unfold circuitAcceptedDensity acceptedDensity
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  rw [raw_branch_density, smul_smul, jointWeight, circuit_born_probability]
  rw [mul_comm]

theorem zero_detection_not_conditionable (model : ReadoutModel)
    (hzero : model.detection.val = 0) : ¬ (0 < probability model.detection) := by
  simp [probability, hzero]

/-- Balanced reported labels do not identify the corruption rate in this model. -/
theorem reported_marginals_ignore_corruption (m₁ m₂ : ReadoutModel)
    (hd : m₁.detection = m₂.detection) (r : BellMeasurement) :
    reportedMass m₁ r = reportedMass m₂ r := by
  rw [reported_mass_formula, reported_mass_formula, hd]

structure QuantumNoisySwappingSuite : Prop where
  mass_complete : ∀ model, acceptedMass model + lostMass model = 1
  success_rate : ∀ model, acceptedMass model = probability model.detection
  raw_density : ∀ model, circuitAcceptedDensity model = acceptedDensity model
  density_formula : ∀ model,
    acceptedDensity model = probability model.detection • labelMixture model
  density_trace : ∀ model, (acceptedDensity model).trace = (acceptedMass model : ℂ)
  fidelity : ∀ model (h : 0 < probability model.detection),
    targetOverlap (conditionalState model h).matrix = 1 - (probability model.corruption : ℂ)
  after_noise : ∀ model (h : 0 < probability model.detection) p,
    targetOverlap (linearChannel p (conditionalState model h).matrix) =
      (1 - (probability p : ℂ)) * (1 - (probability model.corruption : ℂ)) +
        (probability p : ℂ) / 4

theorem verification_suite : QuantumNoisySwappingSuite :=
  ⟨complete_event_mass, accepted_mass_formula, circuit_accepted_density_sound,
    accepted_density_formula, accepted_density_trace, conditional_fidelity,
    conditional_after_depolarization⟩


end QuantumNoisySwapping
