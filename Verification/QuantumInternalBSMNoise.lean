/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoiseTransport
import Verification.QuantumLocalNoisySwapping

/-! Noise at an explicit cut of the CNOT/H Bell analyzer. Computational readout
is defined directly; agreement with the pre-noise instrument is a theorem. -/
noncomputable section
namespace QuantumInternalBSMNoise
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumNoisyVisibility
open QuantumLocalPostNoise QuantumLocalNoisySwapping
open scoped BigOperators ComplexOrder Matrix

theorem cnot_adjoint : cnot.conjTranspose = cnot := by
  ext i j : 2
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [cnot, Matrix.conjTranspose_apply]
  all_goals rfl

theorem cnot_squared : cnot * cnot = 1 := by
  ext i j : 2
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [cnot, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals rfl

def cnotGate : UnitaryGate PairIndex :=
  ⟨cnot, by rw [cnot_adjoint, cnot_squared], by rw [cnot_adjoint, cnot_squared]⟩

def analysisGate : UnitaryGate PairIndex :=
  ⟨analysisUnitary, analysis_unitary_left, analysis_unitary_right⟩

/-- Rightmost prefix acts first; suffix * prefix is the fixed ideal analyzer. -/
structure CircuitCut where
  executed : UnitaryGate PairIndex
  remaining : PairDensity
  factors : remaining * executed.matrix = analysisUnitary

def afterCNOT : CircuitCut := ⟨cnotGate, hadamardControl, rfl⟩
def afterHadamard : CircuitCut := ⟨analysisGate, 1, by simp [analysisGate]⟩

/-- Computational bra on BC, with identities on A,D. -/
def computationalReduction (m : BellMeasurement) : BranchMatrix := fun o i =>
  if o.1 = i.1.1 ∧ o.2 = i.2.2 ∧ outcomeBits m = (i.1.2,i.2.1) then 1 else 0

theorem computational_analysis_reduction (m : BellMeasurement) :
    computationalReduction m * embedBC analysisUnitary = reduction m := by
  ext o i : 2
  simp [computationalReduction, embedBC, reduction, Matrix.mul_apply,
    Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, eq_comm, Prod.ext_iff, analysis_row]

theorem cut_reduction (cut : CircuitCut) (m : BellMeasurement) :
    (computationalReduction m * embedBC cut.remaining) * (centralGate cut.executed).matrix =
      reduction m := by
  change (computationalReduction m * embedBC cut.remaining) * embedBC cut.executed.matrix = _
  rw [Matrix.mul_assoc, embedBC_mul, cut.factors, computational_analysis_reduction]

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- Direct gate-order Kraus: computational bra · suffix · error · prefix. -/
def internalReduction (cut : CircuitCut) (E : CPTP FourIndex κ)
    (m : BellMeasurement) (k : κ) : BranchMatrix :=
  computationalReduction m * embedBC cut.remaining * E.op k * (centralGate cut.executed).matrix

def effectivePre (cut : CircuitCut) (E : CPTP FourIndex κ) : CPTP FourIndex κ :=
  pullback (centralGate cut.executed) E

theorem internal_reduction_transport (cut : CircuitCut) (E : CPTP FourIndex κ)
    (m : BellMeasurement) (k : κ) :
    internalReduction cut E m k = reduction m * (effectivePre cut E).op k := by
  rw [internalReduction, slide_branch, cut_reduction]
  rfl

def internalBranch (cut : CircuitCut) (E : CPTP FourIndex κ)
    (m r : BellMeasurement) (k : κ) : BranchMatrix :=
  correction r * internalReduction cut E m k

theorem internal_branch_transport (cut : CircuitCut) (E : CPTP FourIndex κ)
    (m r : BellMeasurement) (k : κ) :
    internalBranch cut E m r k = branchOperator m r * (effectivePre cut E).op k := by
  rw [internalBranch, internal_reduction_transport, ← Matrix.mul_assoc, branchOperator]

def internalMicro (cut : CircuitCut) (E : CPTP FourIndex κ) (model : Readout)
    (m r : BellMeasurement) (M : FourDensity) : PairDensity :=
  weight model m r • familyMap (internalBranch cut E m r) M

def internalReject (cut : CircuitCut) (E : CPTP FourIndex κ) (model : Readout)
    (M : FourDensity) : PairDensity :=
  ∑ m, (1 - model.detection m) • familyMap (internalReduction cut E m) M

def internalOutcome (cut : CircuitCut) (E : CPTP FourIndex κ) (model : Readout) :
    Outcome → FourDensity → PairDensity
  | none => internalReject cut E model
  | some r => fun M => ∑ m, internalMicro cut E model m r M

theorem internal_micro_refinement (cut : CircuitCut) (E : CPTP FourIndex κ) (model : Readout)
    (m r : BellMeasurement) (M : FourDensity) :
    internalMicro cut E model m r M = microMap model m r ((effectivePre cut E).map M) := by
  simp only [internalMicro, familyMap, internal_branch_transport, microMap, CPTP.map,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem internal_reject_refinement (cut : CircuitCut) (E : CPTP FourIndex κ) (model : Readout)
    (M : FourDensity) :
    internalReject cut E model M = lostMap model ((effectivePre cut E).map M) := by
  simp only [internalReject, familyMap, internal_reduction_transport, lostMap, CPTP.map,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem internal_outcome_refinement (cut : CircuitCut) (E : CPTP FourIndex κ) (model : Readout)
    (o : Outcome) (M : FourDensity) :
    internalOutcome cut E model o M = outcomeMap model o ((effectivePre cut E).map M) := by
  cases o <;> simp only [internalOutcome, outcomeMap, internal_reject_refinement,
    internal_micro_refinement, reportedMap]

theorem internal_outcome_noisy_bridge (cut : CircuitCut) (E : CPTP FourIndex κ)
    (model : Readout) (o : Outcome) :
    internalOutcome cut E model o =
      noisyOutcome (effectivePre cut E) (fun _ => identityChannel PairIndex) model o := by
  funext M
  rw [internal_outcome_refinement]
  cases o <;> simp [noisyOutcome, noisyReject, noisyReported, noisyMicro, outcomeMap, reportedMap]

theorem internal_outcome_cp (cut : CircuitCut) (E : CPTP FourIndex κ)
    (model : Readout) (o : Outcome) : IsCP (internalOutcome cut E model o) := by
  rw [internal_outcome_noisy_bridge]
  exact noisy_outcome_cp _ _ _ _

theorem internal_total_trace (cut : CircuitCut) (E : CPTP FourIndex κ)
    (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, internalOutcome cut E model o M).trace = M.trace := by
  simp only [internal_outcome_refinement]
  rw [outcome_total_trace, CPTP.trace]

/-- Isotropic central noise is the special case that needs no change of channel map. -/
theorem internal_depolarizing_outcome (cut : CircuitCut) (g : Visibility)
    (model : Readout) (o : Outcome) (M : FourDensity) :
    internalOutcome cut (centralChannel (depolarizing g)) model o M =
      outcomeMap model o ((centralChannel (depolarizing g)).map M) := by
  rw [internal_outcome_refinement, effectivePre, central_depolarizing_transport]

def internalAccepted (cut : CircuitCut) (E : CPTP FourIndex κ)
    (post : BellMeasurement → CPTP PairIndex ι) (model : Readout) (M : FourDensity) :
    PairDensity := ∑ r, (post r).map (internalOutcome cut E model (some r) M)

theorem internal_accepted_refinement (cut : CircuitCut) (E : CPTP FourIndex κ)
    (post : BellMeasurement → CPTP PairIndex ι) (model : Readout) (M : FourDensity) :
    internalAccepted cut E post model M = noisyAccepted (effectivePre cut E) post model M := by
  simp only [internalAccepted, internalOutcome, internal_micro_refinement, CPTP.map_sum,
    noisyAccepted, noisyReported, noisyMicro]

theorem internal_depolarizing_accepted (cut : CircuitCut) (g : Visibility)
    (post : BellMeasurement → CPTP PairIndex ι) (model : Readout) (M : FourDensity) :
    internalAccepted cut (centralChannel (depolarizing g)) post model M =
      noisyAccepted (centralChannel (depolarizing g)) post model M := by
  rw [internal_accepted_refinement]
  simp only [noisyAccepted, noisyReported, noisyMicro, effectivePre,
    central_depolarizing_transport]

theorem internal_local_visibility (cut : CircuitCut) (bsm corr w v : Visibility) :
    internalAccepted cut (centralChannel (depolarizing bsm)) (fun _ => localDepolarizing corr)
      QuantumBellDiagonalSwapping.perfectReadout
      (inputDensity
        (QuantumBellDiagonalSwapping.isotropicDistribution w.val ⟨w.nonnegative,w.le_one⟩)
        (QuantumBellDiagonalSwapping.isotropicDistribution v.val ⟨v.nonnegative,v.le_one⟩)) =
      isotropic (multiplyVisibility corr (multiplyVisibility bsm (multiplyVisibility w v))) := by
  rw [internal_depolarizing_accepted]
  exact local_noisy_visibility_matrix bsm corr w v

/-- The same X on B must not be moved through CNOT without conjugation. -/
def flipControl : PairDensity := fun o i => if o.1 = i.1 + 1 ∧ o.2 = i.2 then 1 else 0

theorem flip_control_unitary : flipControl.conjTranspose * flipControl = 1 := by
  ext i j : 2
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [flipControl, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

theorem flip_control_adjoint : flipControl.conjTranspose = flipControl := by
  ext i j : 2
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [flipControl, Matrix.conjTranspose_apply]
  all_goals rfl

def flipControlGate : UnitaryGate PairIndex :=
  ⟨flipControl, flip_control_unitary,
    by simpa only [flip_control_adjoint] using flip_control_unitary⟩

/-- A control flip transported back through CNOT also flips the target. -/
def flipBoth : PairDensity := fun o i =>
  if o.1 = i.1 + 1 ∧ o.2 = i.2 + 1 then 1 else 0

theorem cnot_transports_control_flip_to_both :
    (pullback cnotGate flipControlGate.channel).op () = flipBoth := by
  change cnot.conjTranspose * flipControl * cnot = flipBoth
  rw [cnot_adjoint]
  ext i j : 2
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [cnot, flipControl, flipBoth, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

/-- On central input |00>, X_B after CNOT gives P(00)=1/2; X_B before gives P(00)=0. -/
theorem naive_noise_relocation_changes_born_probability :
    Complex.normSq ((hadamardControl * flipControl * cnot) (0,0) (0,0)) = 1/2 ∧
    Complex.normSq ((analysisUnitary * flipControl) (0,0) (0,0)) = 0 := by
  norm_num [analysisUnitary, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    hadamardControl, hadamard, flipControl, cnot, Complex.normSq_apply,
    bellCoeff, bellScale, div_pow, Real.sq_sqrt]

structure QuantumInternalBSMNoiseSuite : Prop where
  refinement : ∀ {κ : Type} [Fintype κ] cut (E : CPTP FourIndex κ) model o M,
    internalOutcome cut E model o M = outcomeMap model o ((effectivePre cut E).map M)
  complete_positive : ∀ {κ : Type} [Fintype κ] cut (E : CPTP FourIndex κ) model o,
    IsCP (internalOutcome cut E model o)
  trace_balance : ∀ {κ : Type} [Fintype κ] cut (E : CPTP FourIndex κ) model M,
    (∑ o : Outcome, internalOutcome cut E model o M).trace = M.trace
  placement_boundary :
    Complex.normSq ((hadamardControl * flipControl * cnot) (0,0) (0,0)) = 1/2 ∧
    Complex.normSq ((analysisUnitary * flipControl) (0,0) (0,0)) = 0

theorem verification_suite : QuantumInternalBSMNoiseSuite :=
  ⟨internal_outcome_refinement, internal_outcome_cp, internal_total_trace,
    naive_noise_relocation_changes_born_probability⟩

end QuantumInternalBSMNoise
