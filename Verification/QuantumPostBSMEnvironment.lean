/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumTensorStageEnvironment

/-! A nonfactorizing interaction at the computational measurement cut. It acts on
B and the environment, never on the retained A,D indices. -/
noncomputable section
namespace QuantumPostBSMEnvironment
open QuantumTensorStageEnvironment QuantumDecoupledEnvironment QuantumNoiseTransport
open QuantumGateNoiseComposition QuantumOrderedNoiseComposition QuantumEnvironmentExtension
open QuantumPersistentEnvironment QuantumCorrelatedMemoryBSM QuantumBellDiagonalInputs
open QuantumRectangularSwapping QuantumStateAvailabilityContract QuantumGeneralBellReadout
open QuantumOutcomeInstrument QuantumInternalBSMNoise QuantumBellCircuitRefinement
open QuantumEntanglementSwappingPurificationContract QuantumSwappingInstrument
open scoped BigOperators ComplexOrder Matrix Kronecker

/-- System B is the control; the environment is the target. -/
def flipBE (i : FourIndex × Fin 2) : FourIndex × Fin 2 :=
  (i.1, if i.1.1.2 = 0 then i.2 else 1 - i.2)

theorem flipBE_involutive (i : FourIndex × Fin 2) : flipBE (flipBE i) = i := by
  rcases i with ⟨⟨⟨a,b⟩,cd⟩,q⟩
  fin_cases b <;> fin_cases q <;> simp [flipBE]

theorem flipBE_eq_iff (i j : FourIndex × Fin 2) : flipBE i = j ↔ i = flipBE j := by
  constructor
  · intro h; rw [← h, flipBE_involutive]
  · intro h; rw [h, flipBE_involutive]

def postMatrix : Matrix (FourIndex × Fin 2) (FourIndex × Fin 2) ℂ :=
  fun i j => if flipBE i = j then 1 else 0

theorem post_left (M : JointFourDensity (Fin 2)) (i j) :
    (postMatrix * M) i j = M (flipBE i) j := by
  simp [postMatrix, Matrix.mul_apply]

theorem post_right (M : JointFourDensity (Fin 2)) (i j) :
    (M * postMatrix) i j = M i (flipBE j) := by
  simp [postMatrix, Matrix.mul_apply, flipBE_eq_iff]

theorem post_adjoint : postMatrix.conjTranspose = postMatrix := by
  ext i j : 2
  have h : flipBE j = i ↔ flipBE i = j := by rw [flipBE_eq_iff]; exact eq_comm
  simp only [postMatrix, Matrix.conjTranspose_apply, h]
  split_ifs <;> simp

theorem post_squared : postMatrix * postMatrix = 1 := by
  ext i j : 2
  rw [post_left]
  simp [postMatrix, flipBE_involutive, Matrix.one_apply]

def postBSMCnotBE : UnitaryGate (FourIndex × Fin 2) :=
  ⟨postMatrix, by rw [post_adjoint, post_squared], by rw [post_adjoint, post_squared]⟩

theorem post_channel_entry (N : JointFourDensity (Fin 2)) (i j) :
    postBSMCnotBE.channel.map N i j = N (flipBE i) (flipBE j) := by
  rw [unitary_channel_map]
  change (postMatrix * N * postMatrix.conjTranspose) i j = _
  rw [post_adjoint, post_right, post_left]

/-- No assumption of unitarity on the proposed factors is needed. -/
theorem postBSMCnotBE_not_kronecker_product :
    ¬ ∃ (A : FourDensity) (B : Matrix (Fin 2) (Fin 2) ℂ),
      postBSMCnotBE.matrix = A ⊗ₖ B := by
  rintro ⟨A,B,h⟩
  let i : FourIndex := ((0,0),(0,0))
  let j : FourIndex := ((0,1),(0,0))
  have h00 := congrArg (fun M : JointFourDensity (Fin 2) => M (i,0) (i,0)) h
  have h01 := congrArg (fun M : JointFourDensity (Fin 2) => M (i,0) (i,1)) h
  have h11 := congrArg (fun M : JointFourDensity (Fin 2) => M (j,0) (j,1)) h
  change (1 : ℂ) = A i i * B 0 0 at h00
  change (0 : ℂ) = A i i * B 0 1 at h01
  change (1 : ℂ) = A j j * B 0 1 at h11
  have ha : A i i ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h00
    exact one_ne_zero h00
  have hb : B 0 1 = 0 := (mul_eq_zero.mp h01.symm).resolve_left ha
  simp [hb] at h11

/-- Computational, NOT Bell-basis, reduction: the analyzer is already executed. -/
theorem computational_sandwich_entry (m : BellMeasurement) (M : FourDensity)
    (i j : PairIndex) :
    (computationalReduction m * M * (computationalReduction m).conjTranspose) i j =
      M ((i.1,(outcomeBits m).1),((outcomeBits m).2,i.2))
        ((j.1,(outcomeBits m).1),((outcomeBits m).2,j.2)) := by
  simp [computationalReduction, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Prod.ext_iff, ite_and, ite_mul, mul_ite,
    apply_ite (starRingEnd ℂ), eq_comm]

theorem computational_reduction_post_cancel (m : BellMeasurement)
    (N : JointFourDensity (Fin 2)) :
    computationalReduction m * traceEnvironment (postBSMCnotBE.channel.map N) *
        (computationalReduction m).conjTranspose =
      computationalReduction m * traceEnvironment N * (computationalReduction m).conjTranspose := by
  ext i j : 2
  rw [computational_sandwich_entry, computational_sandwich_entry]
  cases m <;> simp [traceEnvironment, Fin.sum_univ_two, post_channel_entry,
    flipBE, outcomeBits, add_comm]

/-- Pauli correction acts on AD and can be applied after the computational cancellation. -/
theorem corrected_computational_post_cancel (m r : BellMeasurement)
    (N : JointFourDensity (Fin 2)) :
    (correction r * computationalReduction m) *
        traceEnvironment (postBSMCnotBE.channel.map N) *
        (correction r * computationalReduction m).conjTranspose =
      (correction r * computationalReduction m) * traceEnvironment N *
        (correction r * computationalReduction m).conjTranspose := by
  have h := congrArg (fun M : PairDensity => correction r * M * (correction r).conjTranspose)
    (computational_reduction_post_cancel m N)
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

theorem select_branch_postBSMCnotBE_cancel (m r : BellMeasurement)
    (N : JointFourDensity (Fin 2)) :
    traceEnvironment (extend (correction r * computationalReduction m) *
      (postBSMCnotBE.matrix * N * postBSMCnotBE.matrix.conjTranspose) *
      (extend (correction r * computationalReduction m)).conjTranspose) =
    traceEnvironment (extend (correction r * computationalReduction m) * N *
      (extend (correction r * computationalReduction m)).conjTranspose) := by
  rw [trace_environment_sandwich, trace_environment_sandwich, ← unitary_channel_map]
  exact corrected_computational_post_cancel m r N

def postStage : Stage (FourIndex × Fin 2) :=
  ⟨Unit, inferInstance, postBSMCnotBE, identityChannel _⟩

theorem run_postStage (ss : List (Stage (FourIndex × Fin 2)))
    (N : JointFourDensity (Fin 2)) :
    run (ss ++ [postStage]) N = postBSMCnotBE.channel.map (run ss N) := by
  rw [run_append]
  change (identityChannel _).map
    (postBSMCnotBE.matrix * run ss N * postBSMCnotBE.matrix.conjTranspose) = _
  rw [QuantumGateNoiseComposition.identity_map, unitary_channel_map]

/-- Invariance holds after ANY preceding joint dynamics, not only an ideal analyzer. -/
theorem post_interaction_outcome_invariant (ss : List (Stage (FourIndex × Fin 2)))
    (model : Readout) (o : Outcome) (N : JointFourDensity (Fin 2)) :
    reducedJointOutcome (ss ++ [postStage]) model o N = reducedJointOutcome ss model o N := by
  cases o with
  | none =>
    change reducedJointReject _ _ _ = reducedJointReject _ _ _
    rw [reduced_reject_run, reduced_reject_run, run_postStage]
    simp only [computational_reduction_post_cancel]
  | some r =>
    rw [reduced_outcome_some, reduced_outcome_some]
    simp only [reduced_micro_run, run_postStage, corrected_computational_post_cancel]

def baseBSMStages : List (Stage FourIndex) :=
  QuantumMultiStageBSM.bsmStages (identityChannel _) (identityChannel _)

def postCoupledBSMStages : List (Stage (FourIndex × Fin 2)) :=
  extendStages baseBSMStages ++ [postStage]

theorem postBSMCnotBE_preserves_all_reducedJointOutcomes (model : Readout) (o : Outcome)
    (N : JointFourDensity (Fin 2)) :
    reducedJointOutcome postCoupledBSMStages model o N =
      QuantumMultiStageBSM.outcome baseBSMStages model o (traceEnvironment N) := by
  rw [postCoupledBSMStages, post_interaction_outcome_invariant,
    extendStages_outcome_depends_only_on_system_marginal]

/-- Product input at the computational-measurement cut: B is plus, E is zero. -/
def probeKet (i : FourIndex × Fin 2) : ℂ :=
  if i.1.1.1 = 0 ∧ i.1.2.1 = 0 ∧ i.1.2.2 = 0 ∧ i.2 = 0 then bellCoeff else 0

def probeState : JointFourDensity (Fin 2) := Matrix.vecMulVec probeKet (star probeKet)

def coupledKet (i : FourIndex × Fin 2) : ℂ := probeKet (flipBE i)

theorem probeState_positive : probeState.PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem probeState_trace_one : probeState.trace = 1 := by
  norm_num [probeState, probeKet, Matrix.trace, Matrix.diag, Matrix.vecMulVec,
    Fintype.sum_prod_type, Fin.sum_univ_two, ← pow_two, bellCoeff_sq]

theorem probeState_coupled_pure :
    postBSMCnotBE.channel.map probeState = Matrix.vecMulVec coupledKet (star coupledKet) := by
  ext i j : 2
  rw [post_channel_entry]
  rfl

/-- A pure-state tensor-factor obstruction, not a definition of mixed-state separability. -/
theorem coupledKet_not_product :
    ¬ ∃ (u : FourIndex → ℂ) (v : Fin 2 → ℂ), ∀ i q, coupledKet (i,q) = u i * v q := by
  rintro ⟨u,v,h⟩
  let i : FourIndex := ((0,0),(0,0))
  let j : FourIndex := ((0,1),(0,0))
  have h00 := h i 0
  have h01 := h i 1
  have h11 := h j 1
  change (bellCoeff : ℂ) = u i * v 0 at h00
  change (0 : ℂ) = u i * v 1 at h01
  change (bellCoeff : ℂ) = u j * v 1 at h11
  have hc : (bellCoeff : ℂ) ≠ 0 := by
    have hs := bellCoeff_sq
    intro hz
    have hz' : bellCoeff = 0 := by exact_mod_cast hz
    rw [hz'] at hs
    norm_num at hs
  have hu : u i ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h00
    exact hc h00
  have hv : v 1 = 0 := (mul_eq_zero.mp h01.symm).resolve_left hu
  rw [hv, mul_zero] at h11
  exact hc h11

theorem post_changes_joint_probe : postBSMCnotBE.channel.map probeState ≠ probeState := by
  intro h
  have he := congrArg (fun M : JointFourDensity (Fin 2) =>
    M (((0,0),(0,0)),0) (((0,1),(0,0)),0)) h
  norm_num [post_channel_entry, probeState, Matrix.vecMulVec, probeKet, flipBE,
    ← pow_two, bellCoeff_sq] at he

structure QuantumPostBSMEnvironmentSuite : Prop where
  nonfactorizing : ¬ ∃ (A : FourDensity) (B : Matrix (Fin 2) (Fin 2) ℂ),
    postBSMCnotBE.matrix = A ⊗ₖ B
  invariant : ∀ (ss : List (Stage (FourIndex × Fin 2))) model o N,
    reducedJointOutcome (ss ++ [postStage]) model o N = reducedJointOutcome ss model o N
  valid_probe : probeState.PosSemidef ∧ probeState.trace = 1
  joint_change : postBSMCnotBE.channel.map probeState ≠ probeState
  pure_nonproduct : ¬ ∃ (u : FourIndex → ℂ) (v : Fin 2 → ℂ),
    ∀ i q, coupledKet (i,q) = u i * v q

theorem verification_suite : QuantumPostBSMEnvironmentSuite :=
  ⟨postBSMCnotBE_not_kronecker_product, post_interaction_outcome_invariant,
    ⟨probeState_positive, probeState_trace_one⟩, post_changes_joint_probe, coupledKet_not_product⟩

end QuantumPostBSMEnvironment
