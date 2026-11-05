/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumEnvironmentExtension
import Verification.QuantumMultiStageBSM

/-! Direct Bell instrumentation with a retained environment across internal gates.
Environment elimination is performed branchwise, after joint evolution and readout. -/
noncomputable section
namespace QuantumMemoryBSM
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumInternalBSMNoise
open QuantumOrderedNoiseComposition QuantumPersistentEnvironment QuantumEnvironmentExtension
open QuantumMultiStageBSM QuantumNoisyVisibility
open scoped BigOperators ComplexOrder Matrix

variable {e κ ι : Type} [Fintype e] [DecidableEq e] [Fintype κ] [Fintype ι]

/-- Joint path includes all gate/noise operations, without intermediate environment reset. -/
def jointReduction (ss : List (Stage (FourIndex × e))) (m : BellMeasurement) (p : Paths ss) :
    Matrix (PairIndex × e) (FourIndex × e) ℂ :=
  extend (computationalReduction m) * (direct ss).op p

def jointBranch (ss : List (Stage (FourIndex × e))) (m r : BellMeasurement) (p : Paths ss) :
    Matrix (PairIndex × e) (FourIndex × e) ℂ :=
  extend (correction r) * jointReduction ss m p

def pathReduction (ss : List (Stage (FourIndex × e))) (q : e) (m : BellMeasurement)
    (pr : Paths ss × e) : BranchMatrix :=
  select (n := PairIndex) pr.2 * jointReduction ss m pr.1 * insert (n := FourIndex) q

def pathBranch (ss : List (Stage (FourIndex × e))) (q : e) (m r : BellMeasurement)
    (pr : Paths ss × e) : BranchMatrix :=
  select (n := PairIndex) pr.2 * jointBranch ss m r pr.1 * insert (n := FourIndex) q

/-- Effective input channel is obtained from the WHOLE joint circuit, not stagewise marginals. -/
def effectivePre (ss : List (Stage (FourIndex × e))) (q : e) : CPTP FourIndex (Paths ss × e) :=
  reduced (effective ss) q

theorem path_reduction_bridge (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (m : BellMeasurement) (pr : Paths ss × e) :
    pathReduction ss q m pr = reduction m * (effectivePre ss q).op pr := by
  unfold pathReduction jointReduction
  rw [path_factorization, h, ← Matrix.mul_assoc (extend _) (extend _), extend_mul,
    computational_analysis_reduction]
  rw [← Matrix.mul_assoc (select _), select_extend]
  simp only [effectivePre, reduced, Matrix.mul_assoc]

theorem path_branch_bridge (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (m r : BellMeasurement) (pr : Paths ss × e) :
    pathBranch ss q m r pr = branchOperator m r * (effectivePre ss q).op pr := by
  unfold pathBranch jointBranch
  rw [← Matrix.mul_assoc (select _), select_extend]
  have hp := congrArg (fun A : BranchMatrix => correction r * A)
    (path_reduction_bridge ss q h m pr)
  simpa only [pathReduction, branchOperator, Matrix.mul_assoc] using hp

/-- Joint outputs still retain the environment in each measurement branch. -/
def jointMicro (ss : List (Stage (FourIndex × e))) (model : Readout) (m r : BellMeasurement)
    (M : Matrix (FourIndex × e) (FourIndex × e) ℂ) : Matrix (PairIndex × e) (PairIndex × e) ℂ :=
  (weight model m r : ℂ) • ∑ p, jointBranch ss m r p * M * (jointBranch ss m r p).conjTranspose

def jointReject (ss : List (Stage (FourIndex × e))) (model : Readout)
    (M : Matrix (FourIndex × e) (FourIndex × e) ℂ) : Matrix (PairIndex × e) (PairIndex × e) ℂ :=
  ∑ m, ((1 - model.detection m : ℝ) : ℂ) •
    ∑ p, jointReduction ss m p * M * (jointReduction ss m p).conjTranspose

def jointOutcome (ss : List (Stage (FourIndex × e))) (model : Readout) :
    Outcome → Matrix (FourIndex × e) (FourIndex × e) ℂ →
      Matrix (PairIndex × e) (PairIndex × e) ℂ
  | none => jointReject ss model
  | some r => fun M => ∑ m, jointMicro ss model m r M

/-- Reduced direct Kraus sums, defined independently of partial trace and effective input noise. -/
def micro (ss : List (Stage (FourIndex × e))) (q : e) (model : Readout)
    (m r : BellMeasurement) (M : FourDensity) : PairDensity :=
  (weight model m r : ℂ) • familyMap (pathBranch ss q m r) M

def reject (ss : List (Stage (FourIndex × e))) (q : e) (model : Readout)
    (M : FourDensity) : PairDensity :=
  ∑ m, ((1 - model.detection m : ℝ) : ℂ) • familyMap (pathReduction ss q m) M

def outcome (ss : List (Stage (FourIndex × e))) (q : e) (model : Readout) :
    Outcome → FourDensity → PairDensity
  | none => reject ss q model
  | some r => fun M => ∑ m, micro ss q model m r M

theorem micro_partial_trace (ss : List (Stage (FourIndex × e))) (q : e)
    (model : Readout) (m r : BellMeasurement) (M : FourDensity) :
    traceEnvironment (jointMicro ss model m r (prepare q M)) = micro ss q model m r M := by
  rw [jointMicro, trace_environment_smul, branch_partial_trace]
  rfl

theorem reject_partial_trace (ss : List (Stage (FourIndex × e))) (q : e)
    (model : Readout) (M : FourDensity) :
    traceEnvironment (jointReject ss model (prepare q M)) = reject ss q model M := by
  rw [jointReject, trace_environment_sum]
  simp only [trace_environment_smul, branch_partial_trace]
  rfl

theorem outcome_partial_trace (ss : List (Stage (FourIndex × e))) (q : e)
    (model : Readout) (o : Outcome) (M : FourDensity) :
    traceEnvironment (jointOutcome ss model o (prepare q M)) = outcome ss q model o M := by
  cases o <;> simp only [jointOutcome, outcome, reject_partial_trace, trace_environment_sum,
    micro_partial_trace]

theorem micro_bridge (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (m r : BellMeasurement) (M : FourDensity) :
    micro ss q model m r M = microMap model m r ((effectivePre ss q).map M) := by
  simp only [micro, familyMap, path_branch_bridge ss q h, microMap, CPTP.map,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem reject_bridge (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (M : FourDensity) :
    reject ss q model M = lostMap model ((effectivePre ss q).map M) := by
  simp only [reject, familyMap, path_reduction_bridge ss q h, lostMap, CPTP.map,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem outcome_bridge (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome ss q model o M = outcomeMap model o ((effectivePre ss q).map M) := by
  cases o <;> simp only [outcome, outcomeMap, reject_bridge ss q h, micro_bridge ss q h,
    reportedMap]

theorem outcome_noisy_bridge (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (model : Readout) (o : Outcome) :
    outcome ss q model o =
      noisyOutcome (effectivePre ss q) (fun _ => identityChannel PairIndex) model o := by
  funext M
  rw [outcome_bridge ss q h]
  cases o <;> simp [noisyOutcome, noisyReject, noisyReported, noisyMicro, outcomeMap, reportedMap]

theorem outcome_cp (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (model : Readout) (o : Outcome) :
    IsCP (outcome ss q model o) := by
  rw [outcome_noisy_bridge ss q h]
  exact noisy_outcome_cp _ _ _ _

theorem total_trace (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, outcome ss q model o M).trace = M.trace := by
  simp only [outcome_bridge ss q h]
  rw [outcome_total_trace, CPTP.trace]

/-- The operational joint run agrees with the effective system channel after final trace. -/
theorem joint_run_refinement (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (M : FourDensity) :
    traceEnvironment (run ss (prepare q M)) = embedBC analysisUnitary *
      (effectivePre ss q).map M * (embedBC analysisUnitary).conjTranspose := by
  rw [run_effective, h, trace_environment_sandwich, ← reduced_map]
  rfl

theorem outcome_positive (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (o : Outcome) (M : FourDensity) (hM : M.PosSemidef) :
    (outcome ss q model o M).PosSemidef := by
  rw [outcome_bridge ss q h]
  exact QuantumOutcomeInstrument.outcome_positive _ _ _ ((effectivePre ss q).positive M hM)

theorem outcome_zero_iff (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (o : Outcome) (M : FourDensity) (hM : M.PosSemidef) :
    (outcome ss q model o M).trace.re = 0 ↔ outcome ss q model o M = 0 :=
  QuantumNullConditioning.psd_zero_probability_iff _ (outcome_positive ss q h model o M hM)

theorem joint_total_trace (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, jointOutcome ss model o (prepare q M)).trace = M.trace := by
  rw [← trace_environment_trace, trace_environment_sum]
  simp only [outcome_partial_trace]
  exact total_trace ss q h model M

/-- CNOT then joint E, H then joint F; the SAME environment is present in both. -/
def memoryStages (E : CPTP (FourIndex × e) κ) (F : CPTP (FourIndex × e) ι) :
    List (Stage (FourIndex × e)) :=
  [⟨κ, inferInstance, extendGate (centralGate cnotGate), E⟩,
   ⟨ι, inferInstance, extendGate (centralGate hGate), F⟩]

theorem memory_ideal (E : CPTP (FourIndex × e) κ) (F : CPTP (FourIndex × e) ι) :
    (ideal (memoryStages E F)).matrix = extend (embedBC analysisUnitary) := by
  change (1 * extend (embedBC hGate.matrix)) * extend (embedBC cnot) = _
  rw [Matrix.one_mul, extend_mul, h_gate_matrix, embedBC_mul]
  rfl

theorem memory_run (E : CPTP (FourIndex × e) κ) (F : CPTP (FourIndex × e) ι)
    (M : Matrix (FourIndex × e) (FourIndex × e) ℂ) :
    run (memoryStages E F) M =
      F.map (extend (embedBC hadamardControl) *
        E.map (extend (embedBC cnot) * M * (extend (embedBC cnot)).conjTranspose) *
        (extend (embedBC hadamardControl)).conjTranspose) := by
  simp only [memoryStages, run, extendGate, centralGate, cnotGate, h_gate_matrix]

theorem memory_outcome_bridge (E : CPTP (FourIndex × e) κ) (F : CPTP (FourIndex × e) ι)
    (q : e) (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome (memoryStages E F) q model o M =
      outcomeMap model o ((effectivePre (memoryStages E F) q).map M) :=
  outcome_bridge _ q (memory_ideal E F) model o M

def accepted (ss : List (Stage (FourIndex × e))) (q : e)
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (M : FourDensity) :
    PairDensity := ∑ r, (post r).map (outcome ss q model (some r) M)

theorem accepted_bridge (ss : List (Stage (FourIndex × e))) (q : e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (M : FourDensity) :
    accepted ss q post model M = noisyAccepted (effectivePre ss q) post model M := by
  simp only [accepted, outcome, micro_bridge ss q h, CPTP.map_sum,
    noisyAccepted, noisyReported, noisyMicro]

/-- Exact ideal limit; the unused environment is not mistaken for additional decoherence. -/
theorem memory_no_noise (q : e) (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome (memoryStages (identityChannel (FourIndex × e)) (identityChannel (FourIndex × e)))
      q model o M = outcomeMap model o M := by
  rw [memory_outcome_bridge, effectivePre, reduced_map]
  have hid (U : UnitaryGate (FourIndex × e)) (N : Matrix (FourIndex × e) (FourIndex × e) ℂ) :
      (pullback U (identityChannel (FourIndex × e))).map N = N := by
    rw [pullback_map, identity_map]
    calc
      _ = (U.matrix.conjTranspose * U.matrix) * N *
          (U.matrix.conjTranspose * U.matrix) := by simp only [Matrix.mul_assoc]
      _ = N := by rw [U.left]; simp
  change outcomeMap model o (traceEnvironment ((effective
    [⟨Unit, inferInstance, extendGate (centralGate cnotGate), identityChannel (FourIndex × e)⟩,
     ⟨Unit, inferInstance, extendGate (centralGate hGate), identityChannel (FourIndex × e)⟩]).map
       (prepare q M))) = _
  rw [two_stage_effective, hid, hid, trace_environment_prepare]

structure QuantumMemoryBSMSuite : Prop where
  branch_trace : ∀ (ss : List (Stage (FourIndex × Fin 2))) q model o M,
    traceEnvironment (jointOutcome ss model o (prepare q M)) = outcome ss q model o M
  refinement : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
    (E : CPTP (FourIndex × Fin 2) κ) (F : CPTP (FourIndex × Fin 2) ι) q model o M,
    outcome (memoryStages E F) q model o M =
      outcomeMap model o ((effectivePre (memoryStages E F) q).map M)
  trace_balance : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
    (E : CPTP (FourIndex × Fin 2) κ) (F : CPTP (FourIndex × Fin 2) ι) q model M,
    (∑ o : Outcome, outcome (memoryStages E F) q model o M).trace = M.trace

theorem verification_suite : QuantumMemoryBSMSuite :=
  ⟨outcome_partial_trace, memory_outcome_bridge,
    fun E F q => total_trace _ q (memory_ideal E F)⟩

end QuantumMemoryBSM
