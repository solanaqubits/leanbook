/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumDecoupledEnvironment

/-! Independent environment dynamics at every chronological stage. Channel labels
may vary with the stage. Identity specialization is equality of actions, not types. -/
noncomputable section
namespace QuantumTensorStageEnvironment
open QuantumDecoupledEnvironment QuantumNoiseTransport QuantumGateNoiseComposition
open QuantumOrderedNoiseComposition QuantumEnvironmentExtension QuantumPersistentEnvironment
open QuantumCorrelatedMemoryBSM QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumStateAvailabilityContract QuantumGeneralBellReadout QuantumOutcomeInstrument
open scoped BigOperators Matrix Kronecker

variable {n e κ : Type} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]

def tensorGate (U : UnitaryGate n) (V : UnitaryGate e) : UnitaryGate (n × e) where
  matrix := U.matrix ⊗ₖ V.matrix
  left := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, U.left, V.left,
      Matrix.one_kronecker_one]
  right := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, U.right, V.right,
      Matrix.one_kronecker_one]

def tensorStage [Fintype κ] (s : Stage n) (V : UnitaryGate e)
    (E : CPTP e κ) : Stage (n × e) :=
  ⟨s.labels × κ, inferInstance, tensorGate s.gate V, tensorCPTP s.noise E⟩

def stageStep (s : Stage n) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  s.noise.map (s.gate.matrix * M * s.gate.matrix.conjTranspose)

theorem traceEnvironment_tensorGate (U : UnitaryGate n) (V : UnitaryGate e)
    (N : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment ((tensorGate U V).matrix * N * (tensorGate U V).matrix.conjTranspose) =
      U.matrix * traceEnvironment N * U.matrix.conjTranspose := by
  simpa [CPTP.map, tensorCPTP, tensorGate, UnitaryGate.channel, Fintype.sum_prod_type]
    using traceEnvironment_tensorCPTP U.channel V.channel N

theorem traceEnvironment_tensorStage_step [Fintype κ] (s : Stage n) (V : UnitaryGate e)
    (E : CPTP e κ) (N : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment (stageStep (tensorStage s V E) N) = stageStep s (traceEnvironment N) := by
  change traceEnvironment ((tensorCPTP s.noise E).map _) = _
  rw [traceEnvironment_tensorCPTP]
  change s.noise.map (traceEnvironment
    ((tensorGate s.gate V).matrix * N * (tensorGate s.gate V).matrix.conjTranspose)) = _
  rw [traceEnvironment_tensorGate]
  rfl

theorem tensorCPTP_identity_map [Fintype κ] (S : CPTP n κ)
    (N : Matrix (n × e) (n × e) ℂ) :
    (tensorCPTP S (identityChannel e)).map N = (extendCPTP S).map N := by
  simp [CPTP.map, tensorCPTP, extendCPTP, identityChannel, Fintype.sum_prod_type, extend]

theorem tensorStage_identity_step_eq_extendStage (s : Stage n)
    (N : Matrix (n × e) (n × e) ℂ) :
    stageStep (tensorStage s (identityGate e) (identityChannel e)) N =
      stageStep (extendStage (e := e) s) N := by
  unfold stageStep tensorStage extendStage
  rw [tensorCPTP_identity_map]
  rfl

/-- A list of paired stages permits different finite environment label types at every step. -/
def tensorStages (ss : List (Stage n × Stage e)) : List (Stage (n × e)) :=
  ss.map fun st => tensorStage st.1 st.2.gate st.2.noise

theorem traceEnvironment_run_tensorStages (ss : List (Stage n × Stage e))
    (N : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment (run (tensorStages ss) N) = run (ss.map Prod.fst) (traceEnvironment N) := by
  induction ss generalizing N with
  | nil => rfl
  | cons s ss ih =>
    change traceEnvironment (run (tensorStages ss)
      (stageStep (tensorStage s.1 s.2.gate s.2.noise) N)) = _
    rw [ih, traceEnvironment_tensorStage_step]
    rfl

theorem tensorStages_outcome_marginal_reduction (ss : List (Stage FourIndex × Stage e))
    (model : Readout) (o : Outcome) (N : JointFourDensity e) :
    reducedJointOutcome (tensorStages ss) model o N =
      QuantumMultiStageBSM.outcome (ss.map Prod.fst) model o (traceEnvironment N) := by
  cases o with
  | none =>
    change reducedJointReject _ _ _ = QuantumMultiStageBSM.reject _ _ _
    rw [reduced_reject_run, system_reject_run, traceEnvironment_run_tensorStages]
  | some r =>
    rw [reduced_outcome_some]
    simp only [QuantumMultiStageBSM.outcome, reduced_micro_run, system_micro_run,
      traceEnvironment_run_tensorStages]

theorem tensorStages_reducedJointOutcome [Fintype κ] (ss : List (Stage FourIndex))
    (V : UnitaryGate e) (E : CPTP e κ) (model : Readout) (o : Outcome)
    (N : JointFourDensity e) :
    reducedJointOutcome (ss.map fun s => tensorStage s V E) model o N =
      QuantumMultiStageBSM.outcome ss model o (traceEnvironment N) := by
  let env : Stage e := ⟨κ, inferInstance, V, E⟩
  simpa [tensorStages, env, List.map_map, Function.comp_def] using
    tensorStages_outcome_marginal_reduction (ss.map fun s => (s,env)) model o N

theorem tensorStages_identity_run (ss : List (Stage n))
    (N : Matrix (n × e) (n × e) ℂ) :
    run (ss.map fun s => tensorStage s (identityGate e) (identityChannel e)) N =
      run (extendStages ss) N := by
  induction ss generalizing N with
  | nil => rfl
  | cons s ss ih =>
    change run (ss.map _) (stageStep (tensorStage s (identityGate e) (identityChannel e)) N) =
      run (extendStages ss) (stageStep (extendStage s) N)
    rw [tensorStage_identity_step_eq_extendStage, ih]

structure QuantumTensorStageEnvironmentSuite : Prop where
  marginal : ∀ (ss : List (Stage FourIndex × Stage (Fin 2))) model o N,
    reducedJointOutcome (tensorStages ss) model o N =
      QuantumMultiStageBSM.outcome (ss.map Prod.fst) model o (traceEnvironment N)
  identity_action : ∀ (ss : List (Stage (Fin 2))) (N : Matrix (Fin 2 × Fin 2) _ ℂ),
    run (ss.map fun s => tensorStage s (identityGate (Fin 2)) (identityChannel (Fin 2))) N =
      run (extendStages ss) N

theorem verification_suite : QuantumTensorStageEnvironmentSuite :=
  ⟨tensorStages_outcome_marginal_reduction, tensorStages_identity_run⟩

end QuantumTensorStageEnvironment
