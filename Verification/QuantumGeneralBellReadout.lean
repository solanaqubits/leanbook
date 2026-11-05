/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoisyBellInstrument

/-! An arbitrary classical channel after ideal Bell measurement, with
outcome-dependent registration. The stochastic constraints are carried by the
input type; there is no symmetry or equal-efficiency assumption. -/
noncomputable section
namespace QuantumGeneralBellReadout
open QuantumPauliMatrix QuantumPauliDensityBridge QuantumTwoQubitCPTP
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open QuantumNoisyBellInstrument
open scoped BigOperators ComplexOrder Kronecker

structure Readout where
  detection : BellMeasurement → ℝ
  detection_nonneg : ∀ a, 0 ≤ detection a
  detection_le_one : ∀ a, detection a ≤ 1
  confusion : BellMeasurement → BellMeasurement → ℝ
  confusion_nonneg : ∀ a r, 0 ≤ confusion a r
  confusion_sum : ∀ a, ∑ r, confusion a r = 1

theorem confusion_le_one (model : Readout) (a r : BellMeasurement) :
    model.confusion a r ≤ 1 := by
  have h := Finset.single_le_sum (fun s (_hs : s ∈ Finset.univ) =>
    model.confusion_nonneg a s) (Finset.mem_univ r)
  simpa only [model.confusion_sum] using h

def observationWeight (model : Readout) (a : BellMeasurement) : Option BellMeasurement → ℝ
  | none => 1 - model.detection a
  | some r => model.detection a * model.confusion a r

theorem observation_nonnegative (model : Readout) (a : BellMeasurement)
    (o : Option BellMeasurement) : 0 ≤ observationWeight model a o := by
  cases o with
  | none => exact sub_nonneg.mpr (model.detection_le_one a)
  | some r => exact mul_nonneg (model.detection_nonneg a) (model.confusion_nonneg a r)

theorem observation_row_sum (model : Readout) (a : BellMeasurement) :
    ∑ o, observationWeight model a o = 1 := by
  simp [Fintype.sum_option, observationWeight, ← Finset.mul_sum, model.confusion_sum]

/-- v4.8 is a particular stochastic channel, not a change to its existing API. -/
def ofSymmetric (model : ReadoutModel) : Readout where
  detection := fun _ => probability model.detection
  detection_nonneg := fun _ => (probability_bounds _).1
  detection_le_one := fun _ => (probability_bounds _).2
  confusion := QuantumNoisyBellInstrument.confusion model
  confusion_nonneg := confusion_nonnegative model
  confusion_sum := confusion_row_sum model

theorem symmetric_weights (model : ReadoutModel) (a : BellMeasurement)
    (o : Option BellMeasurement) :
    observationWeight (ofSymmetric model) a o =
      QuantumNoisyBellInstrument.observationWeight model a o := by
  cases o <;> rfl

/-- Subnormalized completely positive map for one reported label or event loss. -/
def operation (model : Readout) (o : Option BellMeasurement) (M : PairDensity) : PairDensity :=
  ∑ a, observationWeight model a o •
    (bellProjector a * M * (bellProjector a).conjTranspose)

def branchKraus (model : Readout) (o : Option BellMeasurement)
    (a : BellMeasurement) : PairDensity :=
  (Real.sqrt (observationWeight model a o) : ℂ) • bellProjector a

theorem operation_kraus (model : Readout) (o : Option BellMeasurement) (M : PairDensity) :
    operation model o M = ∑ a, branchKraus model o a * M *
      (branchKraus model o a).conjTranspose := by
  unfold operation branchKraus
  apply Finset.sum_congr rfl
  intro a _
  rw [sqrt_sandwich _ (observation_nonnegative model a o)]
  rfl

theorem all_operations (model : Readout) (M : PairDensity) :
    ∑ o, operation model o M =
      ∑ a, bellProjector a * M * (bellProjector a).conjTranspose := by
  simp only [operation]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, observation_row_sum, one_smul]

theorem trace_total (model : Readout) (M : PairDensity) :
    ∑ o, (operation model o M).trace = M.trace := by
  rw [← Matrix.trace_sum, all_operations, nonselective_trace]

/-- Independently defined block extension of each observed CP map. -/
def instrumentExtension (d : Nat) (model : Readout) (o : Option BellMeasurement)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) :
    Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ := fun a b =>
  operation model o (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2

theorem extension_kraus (d : Nat) (model : Readout) (o : Option BellMeasurement)
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

theorem branch_completely_positive (d : Nat) (model : Readout) (o : Option BellMeasurement)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) (hR : R.PosSemidef) :
    (instrumentExtension d model o R).PosSemidef := by
  rw [extension_kraus]
  exact Matrix.posSemidef_sum _ fun _ _ => hR.mul_mul_conjTranspose_same _

theorem operation_positive (model : Readout) (o : Option BellMeasurement)
    (M : PairDensity) (hM : M.PosSemidef) : (operation model o M).PosSemidef := by
  rw [operation_kraus]
  exact Matrix.posSemidef_sum _ fun _ _ => hM.mul_mul_conjTranspose_same _

/-- Born weights of the subnormalized observed density maps. -/
def outcomeProbability (model : Readout) (o : Option BellMeasurement)
    (ρ : PairState) : ℝ := (operation model o ρ.matrix).trace.re

theorem outcomeProbability_nonnegative (model : Readout) (o : Option BellMeasurement)
    (ρ : PairState) : 0 ≤ outcomeProbability model o ρ :=
  (Complex.nonneg_iff.mp (operation_positive model o ρ.matrix ρ.positive).trace_nonneg).1

theorem outcomeProbability_total (model : Readout) (ρ : PairState) :
    ∑ o, outcomeProbability model o ρ = 1 := by
  have h := congrArg Complex.re (trace_total model ρ.matrix)
  simpa [outcomeProbability, ρ.trace_one] using h

theorem outcomeProbability_le_one (model : Readout) (o : Option BellMeasurement)
    (ρ : PairState) : outcomeProbability model o ρ ≤ 1 := by
  have h := Finset.single_le_sum (fun a (_ha : a ∈ Finset.univ) =>
    outcomeProbability_nonnegative model a ρ) (Finset.mem_univ o)
  simpa only [outcomeProbability_total] using h

theorem symmetric_operation (model : ReadoutModel) (o : Option BellMeasurement)
    (M : PairDensity) :
    operation (ofSymmetric model) o M = QuantumNoisyBellInstrument.operation model o M := by
  simp only [operation, QuantumNoisyBellInstrument.operation, symmetric_weights]

structure QuantumGeneralBellReadoutSuite : Prop where
  stochastic : ∀ model a, ∑ o, observationWeight model a o = 1
  cp : ∀ d model o (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ),
    R.PosSemidef → (instrumentExtension d model o R).PosSemidef
  total_trace : ∀ model M, ∑ o, (operation model o M).trace = M.trace
  probability_total : ∀ model ρ, ∑ o, outcomeProbability model o ρ = 1
  probability_bounds : ∀ model o ρ,
    0 ≤ outcomeProbability model o ρ ∧ outcomeProbability model o ρ ≤ 1
  specialization : ∀ model o M,
    operation (ofSymmetric model) o M = QuantumNoisyBellInstrument.operation model o M

theorem verification_suite : QuantumGeneralBellReadoutSuite :=
  ⟨observation_row_sum, branch_completely_positive, trace_total, outcomeProbability_total,
    fun model o ρ => ⟨outcomeProbability_nonnegative model o ρ,
      outcomeProbability_le_one model o ρ⟩, symmetric_operation⟩

end QuantumGeneralBellReadout
