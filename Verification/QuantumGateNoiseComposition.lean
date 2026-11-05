/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNullConditioning

/-! CPTP noise before the ideal BSM reduction and after message-dependent correction.
Noise location is explicit: pre channels act on the input of the ideal instrument. -/
noncomputable section
namespace QuantumGateNoiseComposition
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGeneralBellReadout (Readout)
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumNullConditioning
open scoped BigOperators ComplexOrder Kronecker Matrix

structure CPTP (n κ : Type*) [Fintype n] [DecidableEq n] [Fintype κ] where
  op : κ → Matrix n n ℂ
  complete : (∑ k, (op k).conjTranspose * op k) = 1

variable {n κ ι : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [Fintype ι]

def CPTP.map (E : CPTP n κ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ k, E.op k * M * (E.op k).conjTranspose

theorem CPTP.positive (E : CPTP n κ) (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    (E.map M).PosSemidef := Matrix.posSemidef_sum _ fun _ _ => hM.mul_mul_conjTranspose_same _

theorem CPTP.trace (E : CPTP n κ) (M : Matrix n n ℂ) : (E.map M).trace = M.trace := by
  simp only [CPTP.map, Matrix.trace_sum]
  have ht (k : κ) : (E.op k * M * (E.op k).conjTranspose).trace =
      ((E.op k).conjTranspose * E.op k * M).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp_rw [ht]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, E.complete, Matrix.one_mul]

theorem CPTP.map_add (E : CPTP n κ) (M N : Matrix n n ℂ) :
    E.map (M + N) = E.map M + E.map N := by
  simp [CPTP.map, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem CPTP.map_smul (E : CPTP n κ) (c : ℂ) (M : Matrix n n ℂ) :
    E.map (c • M) = c • E.map M := by
  simp [CPTP.map, Finset.smul_sum]

def CPTP.linear (E : CPTP n κ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := E.map
  map_add' := E.map_add
  map_smul' := E.map_smul

theorem CPTP.map_sum {α : Type*} [Fintype α] (E : CPTP n κ) (M : α → Matrix n n ℂ) :
    E.map (∑ a, M a) = ∑ a, E.map (M a) := _root_.map_sum E.linear M Finset.univ

def identityChannel (n : Type*) [Fintype n] [DecidableEq n] : CPTP n Unit :=
  ⟨fun _ => 1, by simp⟩

@[simp] theorem identity_map (M : Matrix n n ℂ) : (identityChannel n).map M = M := by
  simp [CPTP.map, identityChannel]

/-- The square channel is CP at every ancillary dimension, with an independent block action. -/
theorem CPTP.cp (E : CPTP n κ) (d : Nat)
    (R : Matrix (Fin d × n) (Fin d × n) ℂ) (hR : R.PosSemidef) :
    (Matrix.of fun (a b : Fin d × n) =>
      E.map (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2).PosSemidef := by
  have heq : (Matrix.of fun (a b : Fin d × n) =>
      E.map (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2) =
      ∑ k, ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ E.op k) * R *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ E.op k).conjTranspose := by
    ext a b : 2
    simp [CPTP.map, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply, apply_ite (starRingEnd ℂ),
      mul_ite]
  rw [heq]
  exact Matrix.posSemidef_sum _ fun _ _ => hR.mul_mul_conjTranspose_same _

variable (pre : CPTP FourIndex κ) (post : BellMeasurement → CPTP PairIndex ι)

def noisyMicro (model : Readout) (m r : BellMeasurement) (M : FourDensity) : PairDensity :=
  (post r).map (microMap model m r (pre.map M))

def compositeKraus (model : Readout) (m r : BellMeasurement) (kj : κ × ι) : BranchMatrix :=
  (post r).op kj.2 * kraus model m r * pre.op kj.1

theorem composite_kraus_weighted (model : Readout) (m r : BellMeasurement) (kj : κ × ι) :
    compositeKraus pre post model m r kj = (Real.sqrt (weight model m r) : ℂ) •
      ((post r).op kj.2 * branchOperator m r * pre.op kj.1) := by
  simp [compositeKraus, kraus]

theorem noisy_micro_kraus (model : Readout) (m r : BellMeasurement) (M : FourDensity) :
    noisyMicro pre post model m r M = familyMap (compositeKraus pre post model m r) M := by
  simp only [noisyMicro, micro_kraus, CPTP.map, Matrix.mul_sum, Matrix.sum_mul,
    familyMap, Fintype.sum_prod_type, compositeKraus, Matrix.conjTranspose_mul]
  rw [Finset.sum_comm]
  simp only [Matrix.mul_assoc]

theorem noisy_micro_cp (model : Readout) (m r : BellMeasurement) :
    IsCP (noisyMicro pre post model m r) := by
  have heq : noisyMicro pre post model m r = familyMap (compositeKraus pre post model m r) :=
    funext (noisy_micro_kraus pre post model m r)
  rw [heq]
  exact family_cp _

theorem post_noise_trace_invariant (model : Readout) (m r : BellMeasurement) (M : FourDensity) :
    (noisyMicro pre post model m r M).trace = (microMap model m r (pre.map M)).trace :=
  (post r).trace _

def noisyReported (model : Readout) (r : BellMeasurement) (M : FourDensity) : PairDensity :=
  ∑ m, noisyMicro pre post model m r M

theorem noisy_reported_cp (model : Readout) (r : BellMeasurement) :
    IsCP (noisyReported pre post model r) := by
  have heq : noisyReported pre post model r =
      familyMap (fun (i : BellMeasurement × (κ × ι)) =>
        compositeKraus pre post model i.1 r i.2) := by
    funext M
    simp only [noisyReported, noisy_micro_kraus, familyMap, Fintype.sum_prod_type]
  rw [heq]
  exact family_cp _

def noisyReject (model : Readout) (M : FourDensity) : PairDensity := lostMap model (pre.map M)

theorem noisy_reject_cp (model : Readout) : IsCP (noisyReject pre model) := by
  have heq : noisyReject pre model = familyMap (fun (i : BellMeasurement × κ) =>
      rejectKraus model i.1 * pre.op i.2) := by
    funext M
    simp only [noisyReject, reject_family, familyMap, CPTP.map, Fintype.sum_prod_type,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [heq]
  exact family_cp _

def noisyOutcome (model : Readout) : Outcome → FourDensity → PairDensity
  | none => noisyReject pre model
  | some r => noisyReported pre post model r

theorem noisy_outcome_cp (model : Readout) (o : Outcome) :
    IsCP (noisyOutcome pre post model o) := by
  cases o with
  | none => exact noisy_reject_cp pre model
  | some r => exact noisy_reported_cp pre post model r

theorem noisy_outcome_trace (model : Readout) (o : Outcome) (M : FourDensity) :
    (noisyOutcome pre post model o M).trace = (outcomeMap model o (pre.map M)).trace := by
  cases o with
  | none => rfl
  | some r => simp [noisyOutcome, noisyReported, Matrix.trace_sum, post_noise_trace_invariant,
      outcomeMap, reportedMap]

theorem noisy_outcome_positive (model : Readout) (o : Outcome) (M : FourDensity)
    (hM : M.PosSemidef) : (noisyOutcome pre post model o M).PosSemidef := by
  cases o with
  | none => exact lost_positive model _ (pre.positive M hM)
  | some r => exact Matrix.posSemidef_sum _ fun m _ =>
      (post r).positive _ (micro_positive model m r _ (pre.positive M hM))

theorem noisy_total_trace (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, noisyOutcome pre post model o M).trace = M.trace := by
  simp only [Matrix.trace_sum, noisy_outcome_trace]
  rw [← Matrix.trace_sum, outcome_total_trace, pre.trace]

def noiseState (ρ : FourState) : FourState :=
  ⟨pre.map ρ.matrix, pre.positive _ ρ.positive, by rw [pre.trace, ρ.trace_one]⟩

theorem noisy_probability (model : Readout) (o : Outcome) (ρ : FourState) :
    (noisyOutcome pre post model o ρ.matrix).trace.re =
      outcomeProbability model o (noiseState pre ρ) := by
  rw [noisy_outcome_trace]
  rfl

theorem noisy_null_iff (model : Readout) (o : Outcome) (ρ : FourState) :
    outcomeProbability model o (noiseState pre ρ) = 0 ↔
      noisyOutcome pre post model o ρ.matrix = 0 := by
  rw [← noisy_probability pre post model o ρ]
  exact psd_zero_probability_iff _ (noisy_outcome_positive pre post model o ρ.matrix ρ.positive)

theorem ideal_noise_refinement (model : Readout) (o : Outcome) (M : FourDensity) :
    noisyOutcome (identityChannel FourIndex) (fun _ => identityChannel PairIndex) model o M =
      outcomeMap model o M := by
  cases o <;> simp [noisyOutcome, noisyReject, noisyReported, noisyMicro, outcomeMap, reportedMap]

structure QuantumGateNoiseCompositionSuite : Prop where
  cp : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
    (pre : CPTP FourIndex κ) (post : BellMeasurement → CPTP PairIndex ι) model o,
    IsCP (noisyOutcome pre post model o)
  trace : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
    (pre : CPTP FourIndex κ) (post : BellMeasurement → CPTP PairIndex ι) model M,
    (∑ o : Outcome, noisyOutcome pre post model o M).trace = M.trace
  ideal : ∀ model o M,
    noisyOutcome (identityChannel FourIndex) (fun _ => identityChannel PairIndex) model o M =
      outcomeMap model o M

theorem verification_suite : QuantumGateNoiseCompositionSuite :=
  ⟨noisy_outcome_cp, noisy_total_trace, ideal_noise_refinement⟩

end QuantumGateNoiseComposition
