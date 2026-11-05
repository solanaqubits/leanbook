/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumMixedEnvironment
import Verification.QuantumMemoryBSM
import Verification.QuantumMultiStageBSM

/-! Direct Bell instrumentation with a retained environment across internal gates.
Environment elimination is performed branchwise, after joint evolution and readout. -/
noncomputable section
namespace QuantumMixedMemoryBSM
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumInternalBSMNoise
open QuantumOrderedNoiseComposition QuantumPersistentEnvironment QuantumEnvironmentExtension
open QuantumMultiStageBSM QuantumNoisyVisibility QuantumMemoryBSM QuantumMixedEnvironment
open scoped BigOperators ComplexOrder Matrix Kronecker

variable {e κ ι : Type} [Fintype e] [DecidableEq e] [Fintype κ] [Fintype ι]

def pathReduction (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e) (m : BellMeasurement)
    (pr : e × Paths ss × e) : BranchMatrix :=
  select (n := PairIndex) pr.2.2 * jointReduction ss m pr.2.1 * prepareOp (n := FourIndex) σ pr.1

def pathBranch (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e) (m r : BellMeasurement)
    (pr : e × Paths ss × e) : BranchMatrix :=
  select (n := PairIndex) pr.2.2 * jointBranch ss m r pr.2.1 * prepareOp (n := FourIndex) σ pr.1

/-- Effective input channel is obtained from the WHOLE joint circuit, not stagewise marginals. -/
def effectivePre (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e) :
    CPTP FourIndex (e × Paths ss × e) :=
  mixedReduced (effective ss) σ

theorem path_reduction_bridge (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (m : BellMeasurement) (pr : e × Paths ss × e) :
    pathReduction ss σ m pr = reduction m * (effectivePre ss σ).op pr := by
  unfold pathReduction jointReduction
  rw [path_factorization, h, ← Matrix.mul_assoc (extend _) (extend _), extend_mul,
    computational_analysis_reduction]
  rw [← Matrix.mul_assoc (select _), select_extend]
  simp only [effectivePre, mixedReduced, Matrix.mul_assoc]

theorem path_branch_bridge (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (m r : BellMeasurement) (pr : e × Paths ss × e) :
    pathBranch ss σ m r pr = branchOperator m r * (effectivePre ss σ).op pr := by
  unfold pathBranch jointBranch
  rw [← Matrix.mul_assoc (select _), select_extend]
  have hp := congrArg (fun A : BranchMatrix => correction r * A)
    (path_reduction_bridge ss σ h m pr)
  simpa only [pathReduction, branchOperator, Matrix.mul_assoc] using hp

/-- Reduced direct Kraus sums, defined independently of partial trace and effective input noise. -/
def micro (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e) (model : Readout)
    (m r : BellMeasurement) (M : FourDensity) : PairDensity :=
  (weight model m r : ℂ) • familyMap (pathBranch ss σ m r) M

def reject (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e) (model : Readout)
    (M : FourDensity) : PairDensity :=
  ∑ m, ((1 - model.detection m : ℝ) : ℂ) • familyMap (pathReduction ss σ m) M

def outcome (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e) (model : Readout) :
    Outcome → FourDensity → PairDensity
  | none => reject ss σ model
  | some r => fun M => ∑ m, micro ss σ model m r M

theorem micro_partial_trace (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (model : Readout) (m r : BellMeasurement) (M : FourDensity) :
    traceEnvironment (jointMicro ss model m r (M ⊗ₖ σ.matrix)) = micro ss σ model m r M := by
  rw [jointMicro, trace_environment_smul, mixed_branch_partial_trace]
  rfl

theorem reject_partial_trace (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (model : Readout) (M : FourDensity) :
    traceEnvironment (jointReject ss model (M ⊗ₖ σ.matrix)) = reject ss σ model M := by
  rw [jointReject, trace_environment_sum]
  simp only [trace_environment_smul, mixed_branch_partial_trace]
  rfl

theorem outcome_partial_trace (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (model : Readout) (o : Outcome) (M : FourDensity) :
    traceEnvironment (jointOutcome ss model o (M ⊗ₖ σ.matrix)) = outcome ss σ model o M := by
  cases o <;> simp only [jointOutcome, outcome, reject_partial_trace, trace_environment_sum,
    micro_partial_trace]

theorem micro_bridge (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (m r : BellMeasurement) (M : FourDensity) :
    micro ss σ model m r M = microMap model m r ((effectivePre ss σ).map M) := by
  simp only [micro, familyMap, path_branch_bridge ss σ h, microMap, CPTP.map,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem reject_bridge (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (M : FourDensity) :
    reject ss σ model M = lostMap model ((effectivePre ss σ).map M) := by
  simp only [reject, familyMap, path_reduction_bridge ss σ h, lostMap, CPTP.map,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem outcome_bridge (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome ss σ model o M = outcomeMap model o ((effectivePre ss σ).map M) := by
  cases o <;> simp only [outcome, outcomeMap, reject_bridge ss σ h, micro_bridge ss σ h,
    reportedMap]

theorem outcome_noisy_bridge (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (model : Readout) (o : Outcome) :
    outcome ss σ model o =
      noisyOutcome (effectivePre ss σ) (fun _ => identityChannel PairIndex) model o := by
  funext M
  rw [outcome_bridge ss σ h]
  cases o <;> simp [noisyOutcome, noisyReject, noisyReported, noisyMicro, outcomeMap, reportedMap]

theorem outcome_cp (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (model : Readout) (o : Outcome) :
    IsCP (outcome ss σ model o) := by
  rw [outcome_noisy_bridge ss σ h]
  exact noisy_outcome_cp _ _ _ _

theorem total_trace (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, outcome ss σ model o M).trace = M.trace := by
  simp only [outcome_bridge ss σ h]
  rw [outcome_total_trace, CPTP.trace]

/-- The operational joint run agrees with the effective system channel after final trace. -/
theorem joint_run_refinement (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (M : FourDensity) :
    traceEnvironment (run ss (M ⊗ₖ σ.matrix)) = embedBC analysisUnitary *
      (effectivePre ss σ).map M * (embedBC analysisUnitary).conjTranspose := by
  rw [run_effective, h, trace_environment_sandwich, ← mixed_reduced_map]
  rfl

theorem outcome_positive (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (o : Outcome) (M : FourDensity) (hM : M.PosSemidef) :
    (outcome ss σ model o M).PosSemidef := by
  rw [outcome_bridge ss σ h]
  exact QuantumOutcomeInstrument.outcome_positive _ _ _ ((effectivePre ss σ).positive M hM)

theorem outcome_zero_iff (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (o : Outcome) (M : FourDensity) (hM : M.PosSemidef) :
    (outcome ss σ model o M).trace.re = 0 ↔ outcome ss σ model o M = 0 :=
  QuantumNullConditioning.psd_zero_probability_iff _ (outcome_positive ss σ h model o M hM)

theorem joint_total_trace (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, jointOutcome ss model o (M ⊗ₖ σ.matrix)).trace = M.trace := by
  rw [← trace_environment_trace, trace_environment_sum]
  simp only [outcome_partial_trace]
  exact total_trace ss σ h model M


/-- Compatibility with the earlier basis-state environment instrument. -/
theorem pure_basis_outcome (ss : List (Stage (FourIndex × e))) (σ : EnvironmentState e)
    (q : e) (hσ : ∀ a b, σ.matrix a b = if a = q ∧ b = q then 1 else 0)
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome ss σ model o M = QuantumMemoryBSM.outcome ss q model o M := by
  rw [outcome_bridge ss σ h, QuantumMemoryBSM.outcome_bridge ss q h]
  unfold effectivePre QuantumMemoryBSM.effectivePre
  rw [pure_basis_limit _ σ q hσ]

/-- The joint input density, rather than its ensemble representation, determines every branch. -/
theorem outcome_density_extensionality (ss : List (Stage (FourIndex × e)))
    (σ τ : EnvironmentState e) (hστ : σ.matrix = τ.matrix)
    (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome ss σ model o M = outcome ss τ model o M := by
  rw [← outcome_partial_trace, ← outcome_partial_trace, hστ]

theorem memory_outcome_bridge (E : CPTP (FourIndex × e) κ) (F : CPTP (FourIndex × e) ι)
    (σ : EnvironmentState e) (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome (memoryStages E F) σ model o M =
      outcomeMap model o ((effectivePre (memoryStages E F) σ).map M) :=
  outcome_bridge _ σ (memory_ideal E F) model o M

/-- Exact ideal limit; the unused environment is not mistaken for additional decoherence. -/
theorem memory_no_noise (σ : EnvironmentState e) (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome (memoryStages (identityChannel (FourIndex × e)) (identityChannel (FourIndex × e)))
      σ model o M = outcomeMap model o M := by
  rw [memory_outcome_bridge, effectivePre, mixed_reduced_map]
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
       (M ⊗ₖ σ.matrix))) = _
  rw [two_stage_effective, hid, hid, trace_tensor_state]

structure QuantumMixedMemoryBSMSuite : Prop where
  branch_trace : ∀ (ss : List (Stage (FourIndex × Fin 2))) (σ : EnvironmentState (Fin 2))
    model o M,
    traceEnvironment (jointOutcome ss model o (M ⊗ₖ σ.matrix)) = outcome ss σ model o M
  refinement : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
    (E : CPTP (FourIndex × Fin 2) κ) (F : CPTP (FourIndex × Fin 2) ι)
    (σ : EnvironmentState (Fin 2)) model o M,
    outcome (memoryStages E F) σ model o M =
      outcomeMap model o ((effectivePre (memoryStages E F) σ).map M)
  trace_balance : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
    (E : CPTP (FourIndex × Fin 2) κ) (F : CPTP (FourIndex × Fin 2) ι)
    (σ : EnvironmentState (Fin 2)) model M,
    (∑ o : Outcome, outcome (memoryStages E F) σ model o M).trace = M.trace

theorem verification_suite : QuantumMixedMemoryBSMSuite :=
  ⟨outcome_partial_trace, memory_outcome_bridge,
    fun E F σ => total_trace _ σ (memory_ideal E F)⟩

end QuantumMixedMemoryBSM
