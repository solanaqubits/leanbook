/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCorrelatedMemoryBSM

/-! Sufficient conditions for marginal reduction, including independent environment noise.
No input factorization, positivity, or ideal-analyzer hypothesis is needed. -/
noncomputable section
namespace QuantumDecoupledEnvironment
open QuantumBellDiagonalInputs QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumGeneralBellReadout QuantumOutcomeInstrument
open QuantumGateNoiseComposition QuantumOrderedNoiseComposition QuantumNoiseTransport
open QuantumPersistentEnvironment QuantumEnvironmentExtension QuantumCorrelatedMemoryBSM
open QuantumMemoryBSM QuantumRectangularSwapping QuantumInternalBSMNoise QuantumSwappingInstrument
open scoped BigOperators ComplexOrder Matrix Kronecker

variable {n e κ : Type} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]

omit [Fintype n] [DecidableEq n] [Fintype e] in
theorem extend_sum [Fintype κ] (A : κ → Matrix n n ℂ) :
    extend (e := e) (∑ k, A k) = ∑ k, extend (A k) := by
  ext i j : 2
  simp [extend, Matrix.sum_apply, Finset.sum_mul]

/-- The spectator environment is untouched. -/
def extendCPTP [Fintype κ] (C : CPTP n κ) : CPTP (n × e) κ where
  op k := extend (C.op k)
  complete := by
    simp only [extend_adjoint, extend_mul]
    rw [← extend_sum, C.complete, extend_one]

theorem traceEnvironment_extendCPTP [Fintype κ] (C : CPTP n κ)
    (N : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment ((extendCPTP C).map N) = C.map (traceEnvironment N) := by
  simp only [CPTP.map, extendCPTP, trace_environment_sum, trace_environment_sandwich]

def extendStage (s : Stage n) : Stage (n × e) :=
  ⟨s.labels, s.finiteLabels, extendGate s.gate, extendCPTP s.noise⟩

def extendStages (ss : List (Stage n)) : List (Stage (n × e)) :=
  ss.map (extendStage (e := e))

theorem traceEnvironment_extendStages_run (ss : List (Stage n))
    (N : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment (run (extendStages ss) N) = run ss (traceEnvironment N) := by
  induction ss generalizing N with
  | nil => rfl
  | cons s ss ih =>
    change traceEnvironment (run (extendStages ss)
      ((extendCPTP s.noise).map
        (extend s.gate.matrix * N * (extend s.gate.matrix).conjTranspose))) = _
    rw [ih, traceEnvironment_extendCPTP, trace_environment_sandwich]
    rfl

/-- Branch sums can be expressed through chronological evolution even for nonideal circuits. -/
theorem reduced_micro_run (ss : List (Stage (FourIndex × e))) (model : Readout)
    (m r : BellMeasurement) (N : JointFourDensity e) :
    reducedJointMicro ss model m r N = (weight model m r : ℂ) •
      ((correction r * computationalReduction m) * traceEnvironment (run ss N) *
        (correction r * computationalReduction m).conjTranspose) := by
  have h (p : Paths ss) : jointBranch ss m r p =
      extend (correction r * computationalReduction m) * (direct ss).op p := by
    simp only [jointBranch, jointReduction, ← Matrix.mul_assoc, extend_mul]
  have hs : (∑ p, jointBranch ss m r p * N * (jointBranch ss m r p).conjTranspose) =
      extend (correction r * computationalReduction m) * (direct ss).map N *
        (extend (correction r * computationalReduction m)).conjTranspose := by
    simp only [h, CPTP.map, Matrix.conjTranspose_mul, Matrix.mul_sum,
      Matrix.sum_mul, Matrix.mul_assoc]
  rw [reducedJointMicro, jointMicro, hs, trace_environment_smul,
    trace_environment_sandwich, direct_map_run]

theorem reduced_reject_run (ss : List (Stage (FourIndex × e))) (model : Readout)
    (N : JointFourDensity e) : reducedJointReject ss model N =
    ∑ m, ((1 - model.detection m : ℝ) : ℂ) •
      (computationalReduction m * traceEnvironment (run ss N) *
        (computationalReduction m).conjTranspose) := by
  have hs (m : BellMeasurement) :
      (∑ p, jointReduction ss m p * N * (jointReduction ss m p).conjTranspose) =
      extend (computationalReduction m) * (direct ss).map N *
        (extend (computationalReduction m)).conjTranspose := by
    simp only [jointReduction, CPTP.map, Matrix.conjTranspose_mul, Matrix.mul_sum,
      Matrix.sum_mul, Matrix.mul_assoc]
  unfold reducedJointReject jointReject
  simp only [hs, trace_environment_sum, trace_environment_smul,
    trace_environment_sandwich, direct_map_run]

theorem system_micro_run (ss : List (Stage FourIndex)) (model : Readout)
    (m r : BellMeasurement) (M : FourDensity) :
    QuantumMultiStageBSM.micro ss model m r M = (weight model m r : ℂ) •
      ((correction r * computationalReduction m) * run ss M *
        (correction r * computationalReduction m).conjTranspose) := by
  simp only [QuantumMultiStageBSM.micro, QuantumMultiStageBSM.pathBranch,
    QuantumMultiStageBSM.pathReduction, familyMap, ← direct_map_run, CPTP.map,
    Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  rfl

theorem system_reject_run (ss : List (Stage FourIndex)) (model : Readout)
    (M : FourDensity) : QuantumMultiStageBSM.reject ss model M =
    ∑ m, ((1 - model.detection m : ℝ) : ℂ) •
      (computationalReduction m * run ss M * (computationalReduction m).conjTranspose) := by
  simp only [QuantumMultiStageBSM.reject, QuantumMultiStageBSM.pathReduction,
    familyMap, ← direct_map_run, CPTP.map, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  rfl

theorem extendStages_outcome_depends_only_on_system_marginal
    (ss : List (Stage FourIndex)) (model : Readout) (o : Outcome)
    (N : JointFourDensity e) :
    reducedJointOutcome (extendStages ss) model o N =
      QuantumMultiStageBSM.outcome ss model o (traceEnvironment N) := by
  cases o with
  | none =>
    change reducedJointReject _ _ _ = QuantumMultiStageBSM.reject _ _ _
    rw [reduced_reject_run, system_reject_run, traceEnvironment_extendStages_run]
  | some r =>
    rw [reduced_outcome_some]
    simp only [QuantumMultiStageBSM.outcome, reduced_micro_run, system_micro_run,
      traceEnvironment_extendStages_run]

theorem extendStages_same_system_marginal_eq_output
    (ss : List (Stage FourIndex)) (model : Readout) (o : Outcome)
    (N M : JointFourDensity e) (h : traceEnvironment N = traceEnvironment M) :
    reducedJointOutcome (extendStages ss) model o N =
      reducedJointOutcome (extendStages ss) model o M := by
  rw [extendStages_outcome_depends_only_on_system_marginal,
    extendStages_outcome_depends_only_on_system_marginal, h]

/-- Independent tensor-product channels; neither Kraus factor depends on the other system. -/
def tensorCPTP {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂]
    (S : CPTP n κ₁) (E : CPTP e κ₂) : CPTP (n × e) (κ₁ × κ₂) where
  op kr := S.op kr.1 ⊗ₖ E.op kr.2
  complete := by
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Fintype.sum_prod_type]
    have hs : (∑ k, ∑ l, ((S.op k).conjTranspose * S.op k) ⊗ₖ
        ((E.op l).conjTranspose * E.op l)) =
        (∑ k, (S.op k).conjTranspose * S.op k) ⊗ₖ
          (∑ l, (E.op l).conjTranspose * E.op l) := by
      ext i j : 2
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm
    rw [hs, S.complete, E.complete, Matrix.one_kronecker_one]

/-- The trace of the environment block uses trace preservation, not unitality. -/
theorem traceEnvironment_environment_channel {κ₂ : Type} [Fintype κ₂]
    (E : CPTP e κ₂) (N : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment (∑ l, ((1 : Matrix n n ℂ) ⊗ₖ E.op l) * N *
      ((1 : Matrix n n ℂ) ⊗ₖ E.op l).conjTranspose) = traceEnvironment N := by
  ext i j : 2
  have he := E.trace (Matrix.of fun a b => N (i,a) (j,b))
  change (∑ q, (∑ l, ((1 : Matrix n n ℂ) ⊗ₖ E.op l) * N *
      ((1 : Matrix n n ℂ) ⊗ₖ E.op l).conjTranspose) (i,q) (j,q)) = _
  simpa [CPTP.map, Matrix.trace, Matrix.diag, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply,
    apply_ite (starRingEnd ℂ), mul_ite, traceEnvironment] using he

theorem traceEnvironment_tensorCPTP {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂]
    (S : CPTP n κ₁) (E : CPTP e κ₂) (N : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment ((tensorCPTP S E).map N) = S.map (traceEnvironment N) := by
  have hf (k : κ₁) (l : κ₂) : S.op k ⊗ₖ E.op l =
      extend (e := e) (S.op k) * ((1 : Matrix n n ℂ) ⊗ₖ E.op l) := by
    rw [extend, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hm : (tensorCPTP S E).map N =
      (extendCPTP S).map (∑ l, ((1 : Matrix n n ℂ) ⊗ₖ E.op l) * N *
        ((1 : Matrix n n ℂ) ⊗ₖ E.op l).conjTranspose) := by
    simp only [CPTP.map, tensorCPTP, Fintype.sum_prod_type, hf, extendCPTP,
      Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  rw [hm, traceEnvironment_extendCPTP, traceEnvironment_environment_channel]

structure QuantumDecoupledEnvironmentSuite : Prop where
  marginal : ∀ (ss : List (Stage FourIndex)) model o (N : JointFourDensity (Fin 2)),
    reducedJointOutcome (extendStages ss) model o N =
      QuantumMultiStageBSM.outcome ss model o (traceEnvironment N)
  independent_environment : ∀ (S : CPTP (Fin 2) (Fin 2)) (E : CPTP (Fin 2) (Fin 2)) N,
    traceEnvironment ((tensorCPTP S E).map N) = S.map (traceEnvironment N)

theorem verification_suite : QuantumDecoupledEnvironmentSuite :=
  ⟨extendStages_outcome_depends_only_on_system_marginal, traceEnvironment_tensorCPTP⟩

end QuantumDecoupledEnvironment
