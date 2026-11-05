/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumBellDiagonalInputs

/-! Independent Bell-diagonal inputs through the checked swapping circuit and
an arbitrary classical readout with selective loss. Normalized output is defined
only for positive success probability. -/
noncomputable section
namespace QuantumBellDiagonalSwapping
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellCircuitRefinement
open QuantumNoisyBellInstrument QuantumNoisySwapping QuantumGeneralBellReadout
open QuantumBellDiagonalInputs
open scoped BigOperators ComplexOrder

/-- Accepted subnormalized output of one pure input component. -/
def componentDensity (model : Readout) (a b : BellMeasurement) : PairDensity :=
  ∑ m, ∑ r, (model.detection m / 4 * model.confusion m r) •
    bellProjector (bellXor (bellXor (bellXor a b) m) r)

theorem component_positive (model : Readout) (a b : BellMeasurement) :
    (componentDensity model a b).PosSemidef :=
  Matrix.posSemidef_sum _ fun m _ => Matrix.posSemidef_sum _ fun r _ =>
    (pure_pair_positive _).smul
      (mul_nonneg (div_nonneg (model.detection_nonneg m) (by norm_num))
        (model.confusion_nonneg m r))

theorem component_trace (model : Readout) (a b : BellMeasurement) :
    (componentDensity model a b).trace = (QuantumSelectiveSwapping.acceptedMass model : ℂ) := by
  have hs (m : BellMeasurement) : (∑ r, (model.confusion m r : ℂ)) = 1 := by
    exact_mod_cast model.confusion_sum m
  simp [componentDensity, Matrix.trace_sum, Matrix.trace_smul, bell_projector_trace,
    QuantumSelectiveSwapping.accepted_mass_formula, ← Finset.mul_sum, hs]

def acceptedDensity (p q : BellDistribution) (model : Readout) : PairDensity :=
  ∑ a, ∑ b, (p.weight a * q.weight b) • componentDensity model a b

theorem accepted_positive (p q : BellDistribution) (model : Readout) :
    (acceptedDensity p q model).PosSemidef :=
  Matrix.posSemidef_sum _ fun a _ => Matrix.posSemidef_sum _ fun b _ =>
    (component_positive model a b).smul (mul_nonneg (p.nonnegative a) (q.nonnegative b))

theorem accepted_trace (p q : BellDistribution) (model : Readout) :
    (acceptedDensity p q model).trace = (QuantumSelectiveSwapping.acceptedMass model : ℂ) := by
  have hp : (∑ a, (p.weight a : ℂ)) = 1 := by exact_mod_cast p.total
  have hq : (∑ a, (q.weight a : ℂ)) = 1 := by exact_mod_cast q.total
  simp [acceptedDensity, Matrix.trace_sum, Matrix.trace_smul, component_trace,
    mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hp, hq]

/-- Independent sum of actual unnormalized corrected circuit amplitudes. -/
def circuitDensity (p q : BellDistribution) (model : Readout) : PairDensity :=
  ∑ a, ∑ b, ∑ m, ∑ r,
    (p.weight a * q.weight b * QuantumGeneralBellReadout.observationWeight model m (some r)) •
    purePairDensity (correctOuter r (readoutBranch m (productKet a b)))

theorem circuit_density_sound (p q : BellDistribution) (model : Readout) :
    circuitDensity p q model = acceptedDensity p q model := by
  unfold circuitDensity acceptedDensity componentDensity
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro r _
  rw [raw_corrected_density, smul_smul]
  congr 1
  simp only [QuantumGeneralBellReadout.observationWeight]
  ring

def eventMass (p q : BellDistribution) (model : Readout) : ℝ :=
  ∑ m, mixedBornProbability p q m * model.detection m

theorem event_mass_formula (p q : BellDistribution) (model : Readout) :
    eventMass p q model = QuantumSelectiveSwapping.acceptedMass model := by
  simp only [eventMass, mixed_born_probability, QuantumSelectiveSwapping.accepted_mass_formula]
  apply Finset.sum_congr rfl
  intro m _
  ring

def conditionalState (p q : BellDistribution) (model : Readout)
    (h : 0 < QuantumSelectiveSwapping.acceptedMass model) : PairState where
  matrix := (QuantumSelectiveSwapping.acceptedMass model)⁻¹ • acceptedDensity p q model
  positive := (accepted_positive p q model).smul (le_of_lt (inv_pos.mpr h))
  trace_one := by
    rw [Matrix.trace_smul, accepted_trace]
    simp [Complex.real_smul, ne_of_gt h]

theorem targetOverlap_sum {α : Type*} (s : Finset α) (f : α → PairDensity) :
    targetOverlap (∑ i ∈ s, f i) = ∑ i ∈ s, targetOverlap (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [targetOverlap]
  | @insert i s hi ih => simp [hi, targetOverlap_add, ih]

theorem projector_overlap (a : BellMeasurement) :
    targetOverlap (bellProjector a) = if a = .phiPlus then 1 else 0 := by
  have h := miscorrection_overlap a .phiPlus
  rw [correctedDensity, correctedKet_eq, correction_density] at h
  have hx : bellXor a .phiPlus = a := by cases a <;> rfl
  simpa only [hx] using h

/-- Probability mass of the target Bell component after correction, not simply
probability of a correctly reported label when the input pairs are noisy. -/
def targetMass (p q : BellDistribution) (model : Readout) : ℝ :=
  ∑ a, ∑ b, p.weight a * q.weight b *
    (∑ m, ∑ r, (model.detection m / 4 * model.confusion m r) *
      if bellXor (bellXor (bellXor a b) m) r = .phiPlus then 1 else 0)

theorem accepted_overlap (p q : BellDistribution) (model : Readout) :
    targetOverlap (acceptedDensity p q model) = (targetMass p q model : ℂ) := by
  simp [acceptedDensity, componentDensity, targetOverlap_sum, targetOverlap_real_smul,
    projector_overlap, targetMass, apply_ite]

theorem conditional_fidelity (p q : BellDistribution) (model : Readout)
    (h : 0 < QuantumSelectiveSwapping.acceptedMass model) :
    targetOverlap (conditionalState p q model h).matrix =
      ((targetMass p q model / QuantumSelectiveSwapping.acceptedMass model : ℝ) : ℂ) := by
  change targetOverlap (_ • _) = _
  rw [targetOverlap_real_smul, accepted_overlap]
  push_cast
  ring

/-- Perfect registration and faithful classical reporting. -/
def perfectReadout : Readout where
  detection := fun _ => 1
  detection_nonneg := fun _ => by norm_num
  detection_le_one := fun _ => le_refl 1
  confusion := fun m r => if m = r then 1 else 0
  confusion_nonneg := by intro m r; split_ifs <;> norm_num
  confusion_sum := by intro m; simp

theorem perfect_mass : QuantumSelectiveSwapping.acceptedMass perfectReadout = 1 := by
  rw [QuantumSelectiveSwapping.accepted_mass_formula, sum_bell]
  norm_num [perfectReadout]

theorem perfect_component (a b : BellMeasurement) :
    componentDensity perfectReadout a b = bellProjector (bellXor a b) := by
  unfold componentDensity
  simp only [perfectReadout, mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, xor_cancel]
  rw [sum_bell]
  simp only [← add_smul]
  norm_num

/-- XOR convolution of complete Bell-label distributions, derived from the circuit. -/
def idealDensity (p q : BellDistribution) : PairDensity :=
  ∑ a, ∑ b, (p.weight a * q.weight b) • bellProjector (bellXor a b)

theorem ideal_density_from_circuit (p q : BellDistribution) :
    circuitDensity p q perfectReadout = idealDensity p q := by
  rw [circuit_density_sound]
  simp only [acceptedDensity, perfect_component, idealDensity]

theorem ideal_conditional_density (p q : BellDistribution) :
    (conditionalState p q perfectReadout (by rw [perfect_mass]; norm_num)).matrix =
      idealDensity p q := by
  change (QuantumSelectiveSwapping.acceptedMass perfectReadout)⁻¹ • _ = _
  rw [perfect_mass]
  simp [acceptedDensity, perfect_component, idealDensity]

theorem ideal_fidelity (p q : BellDistribution) :
    targetOverlap (idealDensity p q) = ((∑ a, p.weight a * q.weight a : ℝ) : ℂ) := by
  simp [idealDensity, targetOverlap_sum, targetOverlap_real_smul, projector_overlap, xor_zero_iff]

def pointDistribution (a : BellMeasurement) : BellDistribution where
  weight := fun b => if b = a then 1 else 0
  nonnegative := by intro b; split_ifs <;> norm_num
  total := by simp

theorem ideal_inputs_recover_v49 (model : Readout) :
    acceptedDensity (pointDistribution .phiPlus) (pointDistribution .phiPlus) model =
      QuantumSelectiveSwapping.acceptedDensity model := by
  simp only [acceptedDensity, pointDistribution, one_smul,
    mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold componentDensity QuantumSelectiveSwapping.acceptedDensity
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro r _
  rw [QuantumSelectiveSwapping.joint_formula]
  congr 1
  rw [correctedDensity, correctedKet_eq, correction_density]
  cases m <;> cases r <;> rfl


def uniformDistribution : BellDistribution where
  weight := fun _ => 1 / 4
  nonnegative := fun _ => by norm_num
  total := by rw [sum_bell]; norm_num

set_option maxHeartbeats 2000000 in
-- Four Bell-label permutations are checked at sixteen matrix entries.
theorem uniform_bell_sum (b : BellMeasurement) :
    (∑ a, (1 / 4 : ℝ) • bellProjector (bellXor a b)) = maximallyMixed := by
  rw [sum_bell]
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  cases b <;> fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    norm_num [bellProjector, purePairDensity, Matrix.vecMulVec, bellXor, fromBits,
      zBit, xBit, bellKet, maximallyMixed, Complex.real_smul, ← pow_two, bellCoeff_sq]

theorem uniform_input_erases_ideal_output (q : BellDistribution) :
    idealDensity uniformDistribution q = maximallyMixed := by
  unfold idealDensity
  rw [Finset.sum_comm]
  simp only [uniformDistribution]
  have row (b : BellMeasurement) :
      (∑ a, ((1 / 4 : ℝ) * q.weight b) • bellProjector (bellXor a b)) =
        q.weight b • maximallyMixed := by
    simp only [mul_comm (1 / 4 : ℝ), mul_smul]
    rw [← Finset.smul_sum, uniform_bell_sum]
  simp_rw [row]
  rw [← Finset.sum_smul, q.total, one_smul]

/-- A Bell-isotropic (Werner up to a local unitary) family, using real visibility
rather than rounding a product back to the basis-point grid. -/
def isotropicDistribution (w : ℝ) (hw : 0 ≤ w ∧ w ≤ 1) : BellDistribution where
  weight := fun a => match a with
    | .phiPlus => (1 + 3 * w) / 4
    | _ => (1 - w) / 4
  nonnegative := by intro a; cases a <;> dsimp <;> linarith [hw.1, hw.2]
  total := by rw [sum_bell]; dsimp; ring

theorem visibility_product_valid (w v : ℝ) (hw : 0 ≤ w ∧ w ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    0 ≤ w * v ∧ w * v ≤ 1 :=
  ⟨mul_nonneg hw.1 hv.1, mul_le_one₀ hw.2 hv.1 hv.2⟩

set_option maxHeartbeats 2000000 in
-- Entrywise expansion of the two Bell mixtures proves the complete density identity.
theorem isotropic_visibility_product (w v : ℝ)
    (hw : 0 ≤ w ∧ w ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    idealDensity (isotropicDistribution w hw) (isotropicDistribution v hv) =
      density (isotropicDistribution (w * v) (visibility_product_valid w v hw hv)) := by
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    simp [idealDensity, density, sum_bell, isotropicDistribution, bellProjector,
      purePairDensity, Matrix.vecMulVec, bellXor, fromBits, zBit, xBit, bellKet,
      Complex.real_smul] <;> ring

theorem isotropic_output_fidelity (w v : ℝ)
    (hw : 0 ≤ w ∧ w ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    targetOverlap (idealDensity (isotropicDistribution w hw) (isotropicDistribution v hv)) =
      (((1 + 3 * w * v) / 4 : ℝ) : ℂ) := by
  rw [ideal_fidelity, sum_bell]
  simp [isotropicDistribution]
  ring

theorem density_overlap (p : BellDistribution) :
    targetOverlap (density p) = (p.weight .phiPlus : ℂ) := by
  simp [density, targetOverlap_sum, targetOverlap_real_smul, projector_overlap]

/-- Two different error directions with identical target overlap. -/
def halfError (bitError : Bool) : BellDistribution where
  weight := fun a => match a with
    | .phiPlus => 1 / 2
    | .phiMinus => if bitError then 0 else 1 / 2
    | .psiPlus => if bitError then 1 / 2 else 0
    | .psiMinus => 0
  nonnegative := by intro a; cases a <;> cases bitError <;> norm_num
  total := by rw [sum_bell]; cases bitError <;> norm_num

theorem scalar_fidelity_insufficient :
    targetOverlap (density (halfError false)) = (1 / 2 : ℂ) ∧
    targetOverlap (density (halfError true)) = (1 / 2 : ℂ) ∧
    targetOverlap (idealDensity (halfError false) (halfError false)) = (1 / 2 : ℂ) ∧
    targetOverlap (idealDensity (halfError true) (halfError false)) = (1 / 4 : ℂ) := by
  norm_num [density_overlap, ideal_fidelity, sum_bell, halfError]

theorem null_event_density (p q : BellDistribution) (model : Readout)
    (h : QuantumSelectiveSwapping.acceptedMass model = 0) : acceptedDensity p q model = 0 := by
  simp [acceptedDensity, componentDensity, (QuantumSelectiveSwapping.zero_mass_iff model).mp h]

theorem ideal_inputs_conditional (model : Readout)
    (h : 0 < QuantumSelectiveSwapping.acceptedMass model) :
    (conditionalState (pointDistribution .phiPlus) (pointDistribution .phiPlus) model h).matrix =
      (QuantumSelectiveSwapping.conditionalState model h).matrix := by
  change (QuantumSelectiveSwapping.acceptedMass model)⁻¹ • _ = _
  rw [ideal_inputs_recover_v49]
  rfl

structure QuantumBellDiagonalSwappingSuite : Prop where
  circuit : ∀ p q model, circuitDensity p q model = acceptedDensity p q model
  trace_output : ∀ p q model,
    (acceptedDensity p q model).trace = (QuantumSelectiveSwapping.acceptedMass model : ℂ)
  rate : ∀ p q model, eventMass p q model = QuantumSelectiveSwapping.acceptedMass model
  fidelity : ∀ p q model (h : 0 < QuantumSelectiveSwapping.acceptedMass model),
    targetOverlap (conditionalState p q model h).matrix =
      ((targetMass p q model / QuantumSelectiveSwapping.acceptedMass model : ℝ) : ℂ)
  ideal : ∀ p q, circuitDensity p q perfectReadout = idealDensity p q
  ideal_overlap : ∀ p q,
    targetOverlap (idealDensity p q) = ((∑ a, p.weight a * q.weight a : ℝ) : ℂ)
  mixed_input : ∀ q, idealDensity uniformDistribution q = maximallyMixed
  specialization : ∀ model,
    acceptedDensity (pointDistribution .phiPlus) (pointDistribution .phiPlus) model =
      QuantumSelectiveSwapping.acceptedDensity model

theorem verification_suite : QuantumBellDiagonalSwappingSuite :=
  ⟨circuit_density_sound, accepted_trace, event_mass_formula, conditional_fidelity,
    ideal_density_from_circuit, ideal_fidelity, uniform_input_erases_ideal_output,
    ideal_inputs_recover_v49⟩

end QuantumBellDiagonalSwapping
