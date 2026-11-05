/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumBellCircuitRefinement

/-! Classical postprocessing of ideal Bell measurement: outcome-independent
registration and symmetric misreporting among three wrong labels. Lost events
retain the nonselective measured state. These are modeling assumptions, not
properties inferred for a detector. -/
noncomputable section
namespace QuantumNoisyBellInstrument
open QuantumPauliMatrix QuantumPauliDensityBridge QuantumTwoQubitCPTP
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open QuantumBellCircuitRefinement
open scoped BigOperators ComplexOrder Kronecker

instance bellFintype : Fintype BellMeasurement :=
  ⟨{.phiPlus, .phiMinus, .psiPlus, .psiMinus}, by intro m; cases m <;> simp⟩

theorem sum_bell {α : Type*} [AddCommMonoid α] (f : BellMeasurement → α) :
    ∑ m, f m = f .phiPlus + f .phiMinus + f .psiPlus + f .psiMinus := by
  change (∑ m ∈ ({.phiPlus, .phiMinus, .psiPlus, .psiMinus} : Finset BellMeasurement), f m) = _
  simp [add_assoc]

structure ReadoutModel where
  detection : BoundedBps
  corruption : BoundedBps

/-- A row-stochastic classical channel, conditioned on an event being registered. -/
def confusion (model : ReadoutModel) (actual reported : BellMeasurement) : ℝ :=
  if actual = reported then 1 - probability model.corruption else probability model.corruption / 3

theorem confusion_nonnegative (model : ReadoutModel) (a r : BellMeasurement) :
    0 ≤ confusion model a r := by
  unfold confusion
  split_ifs
  · exact sub_nonneg.mpr (probability_bounds _).2
  · exact div_nonneg (probability_bounds _).1 (by norm_num)

theorem confusion_row_sum (model : ReadoutModel) (a : BellMeasurement) :
    ∑ r, confusion model a r = 1 := by
  rw [sum_bell]
  cases a <;> simp [confusion] <;> ring

theorem confusion_column_sum (model : ReadoutModel) (r : BellMeasurement) :
    ∑ a, confusion model a r = 1 := by
  rw [sum_bell]
  cases r <;> simp [confusion] <;> ring

/-- none is a lost classical event, some r is the reported label. -/
def observationWeight (model : ReadoutModel) (a : BellMeasurement) : Option BellMeasurement → ℝ
  | none => 1 - probability model.detection
  | some r => probability model.detection * confusion model a r

theorem observation_nonnegative (model : ReadoutModel) (a : BellMeasurement)
    (o : Option BellMeasurement) : 0 ≤ observationWeight model a o := by
  cases o with
  | none => exact sub_nonneg.mpr (probability_bounds _).2
  | some r => exact mul_nonneg (probability_bounds _).1 (confusion_nonnegative model a r)

theorem observation_row_sum (model : ReadoutModel) (a : BellMeasurement) :
    ∑ o, observationWeight model a o = 1 := by
  simp [Fintype.sum_option, observationWeight, ← Finset.mul_sum, confusion_row_sum]

def bellProjector (a : BellMeasurement) : PairDensity := purePairDensity (bellKet a)

/-- Subnormalized completely positive map for one reported label or event loss. -/
def operation (model : ReadoutModel) (o : Option BellMeasurement) (M : PairDensity) : PairDensity :=
  ∑ a, observationWeight model a o •
    (bellProjector a * M * (bellProjector a).conjTranspose)

def branchKraus (model : ReadoutModel) (o : Option BellMeasurement)
    (a : BellMeasurement) : PairDensity :=
  (Real.sqrt (observationWeight model a o) : ℂ) • bellProjector a

theorem operation_kraus (model : ReadoutModel) (o : Option BellMeasurement) (M : PairDensity) :
    operation model o M = ∑ a, branchKraus model o a * M *
      (branchKraus model o a).conjTranspose := by
  unfold operation branchKraus
  apply Finset.sum_congr rfl
  intro a _
  rw [sqrt_sandwich _ (observation_nonnegative model a o)]
  rfl

theorem all_operations (model : ReadoutModel) (M : PairDensity) :
    ∑ o, operation model o M =
      ∑ a, bellProjector a * M * (bellProjector a).conjTranspose := by
  simp only [operation]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, observation_row_sum, one_smul]

theorem nonselective_trace (M : PairDensity) :
    (∑ a, bellProjector a * M * (bellProjector a).conjTranspose).trace = M.trace := by
  simp [sum_bell, bellProjector, purePairDensity, Matrix.vecMulVec,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, bellKet]
  ring_nf
  norm_num [bellCoeff_sq, bellCoeff_four]
  ring

theorem trace_total (model : ReadoutModel) (M : PairDensity) :
    ∑ o, (operation model o M).trace = M.trace := by
  rw [← Matrix.trace_sum, all_operations, nonselective_trace]

/-- Independently defined block extension of each observed CP map. -/
def instrumentExtension (d : Nat) (model : ReadoutModel) (o : Option BellMeasurement)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) :
    Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ := fun a b =>
  operation model o (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2

theorem extension_kraus (d : Nat) (model : ReadoutModel) (o : Option BellMeasurement)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) :
    instrumentExtension d model o R = ∑ a,
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ branchKraus model o a) * R *
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ branchKraus model o a).conjTranspose := by
  ext i j : 2
  change operation model o (Matrix.of fun a b => R (i.1,a) (j.1,b)) i.2 j.2 = _
  rw [operation_kraus]
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite (starRingEnd ℂ),
    mul_ite, Finset.sum_add_distrib]

theorem branch_completely_positive (d : Nat) (model : ReadoutModel) (o : Option BellMeasurement)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) (hR : R.PosSemidef) :
    (instrumentExtension d model o R).PosSemidef := by
  rw [extension_kraus]
  exact Matrix.posSemidef_sum _ fun _ _ => hR.mul_mul_conjTranspose_same _

theorem operation_positive (model : ReadoutModel) (o : Option BellMeasurement)
    (M : PairDensity) (hM : M.PosSemidef) : (operation model o M).PosSemidef := by
  rw [operation_kraus]
  exact Matrix.posSemidef_sum _ fun _ _ => hM.mul_mul_conjTranspose_same _

/-- Born weights of the subnormalized observed density maps. -/
def outcomeProbability (model : ReadoutModel) (o : Option BellMeasurement)
    (ρ : PairState) : ℝ := (operation model o ρ.matrix).trace.re

theorem outcomeProbability_nonnegative (model : ReadoutModel) (o : Option BellMeasurement)
    (ρ : PairState) : 0 ≤ outcomeProbability model o ρ :=
  (Complex.nonneg_iff.mp (operation_positive model o ρ.matrix ρ.positive).trace_nonneg).1

theorem outcomeProbability_total (model : ReadoutModel) (ρ : PairState) :
    ∑ o, outcomeProbability model o ρ = 1 := by
  have h := congrArg Complex.re (trace_total model ρ.matrix)
  simpa [outcomeProbability, ρ.trace_one] using h

theorem outcomeProbability_le_one (model : ReadoutModel) (o : Option BellMeasurement)
    (ρ : PairState) : outcomeProbability model o ρ ≤ 1 := by
  have h := Finset.single_le_sum (fun a (_ha : a ∈ Finset.univ) =>
    outcomeProbability_nonnegative model a ρ) (Finset.mem_univ o)
  simpa only [outcomeProbability_total] using h

/-- The projectors used in the noisy instrument come from the checked gate circuit. -/
theorem projector_matches_circuit (m : BellMeasurement) (v : FourKet)
    (a b c d : Fin 2) :
    (∑ i : PairIndex, bellProjector m (b,c) i * v a i.1 i.2 d) =
      undoAnalysis (readoutProject m v) a b c d := by
  rw [instrument_equals_bell_projection]
  simp [bellProjector, purePairDensity, Matrix.vecMulVec, swappingProject,
    swappingContraction, Fintype.sum_prod_type, mul_assoc]
  ring


structure QuantumNoisyBellInstrumentSuite : Prop where
  stochastic : ∀ model a, ∑ o, observationWeight model a o = 1
  weights_nonnegative : ∀ model a o, 0 ≤ observationWeight model a o
  cp : ∀ d model o (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ),
    R.PosSemidef → (instrumentExtension d model o R).PosSemidef
  total_trace : ∀ model M, ∑ o, (operation model o M).trace = M.trace
  probability_total : ∀ model ρ, ∑ o, outcomeProbability model o ρ = 1
  probability_bounds : ∀ model o ρ,
    0 ≤ outcomeProbability model o ρ ∧ outcomeProbability model o ρ ≤ 1
  circuit_bridge : ∀ m v a b c d,
    (∑ i : PairIndex, bellProjector m (b,c) i * v a i.1 i.2 d) =
      undoAnalysis (readoutProject m v) a b c d

theorem verification_suite : QuantumNoisyBellInstrumentSuite :=
  ⟨observation_row_sum, observation_nonnegative, branch_completely_positive,
    trace_total, outcomeProbability_total,
    fun model o ρ => ⟨outcomeProbability_nonnegative model o ρ,
      outcomeProbability_le_one model o ρ⟩, projector_matches_circuit⟩


end QuantumNoisyBellInstrument
