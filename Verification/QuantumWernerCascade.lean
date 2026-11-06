/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCascadedSwapping
import Verification.QuantumCascadeReduction

/-! A concrete perfect-readout specialization of the two-round operator cascade.
Fresh resources and second-round channels are independent of the first message.
This is a matrix refinement, not a definition of the output by a scalar law. -/
noncomputable section
namespace QuantumWernerCascade
open QuantumCascadedSwapping QuantumCorrelatedPostNoise QuantumCorrelatedMemoryBSM
open QuantumGateNoiseComposition QuantumOrderedNoiseComposition QuantumNoiseTransport
open QuantumMixedEnvironment QuantumPersistentEnvironment QuantumEnvironmentExtension
open QuantumDecoupledEnvironment QuantumInternalBSMNoise QuantumCentralDepolarization
open QuantumBellCircuitRefinement QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumStateAvailabilityContract QuantumEntanglementSwappingPurificationContract
open QuantumOutcomeInstrument QuantumSwappingInstrument QuantumNoisyVisibility
open QuantumGeneralBellReadout QuantumBellDiagonalSwapping
open scoped BigOperators ComplexOrder Matrix Kronecker

variable {e κ ι : Type} [Fintype e] [DecidableEq e] [Fintype κ] [Fintype ι]

/-- Noise before the complete Bell analyzer; a distinct, explicitly specified insertion cut. -/
def preStages (E : CPTP FourIndex κ) : List (Stage (FourIndex × e)) :=
  [⟨κ, inferInstance, identityGate _, extendCPTP E⟩,
   ⟨Unit, inferInstance, extendGate (centralGate analysisGate), identityChannel _⟩]

theorem preStages_ideal (E : CPTP FourIndex κ) :
    (ideal (preStages (e := e) E)).matrix = extend (embedBC analysisUnitary) := by
  change (1 * extend (embedBC analysisUnitary)) * 1 = _
  simp

theorem preStages_run (E : CPTP FourIndex κ) (N : JointFourDensity e) :
    traceEnvironment (run (preStages E) N) =
      embedBC analysisUnitary * E.map (traceEnvironment N) *
        (embedBC analysisUnitary).conjTranspose := by
  simp only [preStages, run, identityGate, Matrix.one_mul, Matrix.conjTranspose_one,
    Matrix.mul_one, identity_map, extendGate, centralGate, analysisGate]
  rw [trace_environment_sandwich, traceEnvironment_extendCPTP]

def preRound (E : CPTP FourIndex κ) (post : BellMeasurement → CPTP PairIndex ι)
    (model : Readout) : Round e ι :=
  ⟨preStages E, preStages_ideal E, post, model⟩

theorem preRound_micro (E : CPTP FourIndex κ) (post : BellMeasurement → CPTP PairIndex ι)
    (model : Readout) (m r : BellMeasurement) (N : JointFourDensity e) :
    noisyJointMicro (preStages E) post model m r N =
      noisyMicro E post model m r (traceEnvironment N) := by
  unfold noisyJointMicro noisyMicro
  rw [reduced_micro_run, preStages_run]
  congr 1
  unfold microMap branchOperator
  rw [← computational_analysis_reduction m]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Complex.coe_smul]

theorem preRound_map (E : CPTP FourIndex κ) (post : BellMeasurement → CPTP PairIndex ι)
    (model : Readout) (o : Outcome) (N : JointFourDensity e) :
    ((preRound E post model).branch o).map N =
      noisyOutcome E post model o (traceEnvironment N) := by
  rw [Round.branch_map]
  cases o with
  | some r =>
    change noisyJointOutcome (preStages E) post model (some r) N = _
    rw [noisy_outcome_some]
    simp only [preRound_micro, noisyOutcome, noisyReported]
  | none =>
    change reducedJointReject (preStages E) model N = _
    rw [reduced_reject_run, preStages_run]
    unfold noisyOutcome noisyReject lostMap
    apply Finset.sum_congr rfl
    intro m _
    rw [← computational_analysis_reduction m]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Complex.coe_smul]

/-- Here the correction noise is isotropic depolarization on the full output pair AD. -/
def wernerRound (bsm corr : Visibility) : Round e (Option (PairIndex × PairIndex)) :=
  preRound (centralChannel (depolarizing bsm)) (fun _ => depolarizing corr) perfectReadout

def pairResource (w : Visibility) : EnvironmentState PairIndex :=
  ⟨isotropic w, density_positive _, isotropic_trace w⟩

/-- Uniform resources exclude adaptive postselection from the visibility product formula. -/
def wernerCascade {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b₁ c₁ b₂ c₂ fresh : Visibility)
    (σ₂ : EnvironmentState e₂) :
    Cascade e₁ e₂ (Option (PairIndex × PairIndex)) (Option (PairIndex × PairIndex)) where
  first := wernerRound b₁ c₁
  second := fun _ => wernerRound b₂ c₂
  freshPair := fun _ => pairResource fresh
  freshMemory := fun _ => σ₂

/-- Aggregate only histories delivered in both rounds. Rejection remains in the full instrument. -/
def acceptedCascade {e₁ e₂ κ₁ κ₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] [Fintype κ₁] [Fintype κ₂]
    (C : Cascade e₁ e₂ κ₁ κ₂) (N : JointFourDensity e₁) : PairDensity :=
  ∑ r₁, ∑ r₂, (cascadeBranch C r₁ (some r₂)).map N

theorem wernerRound_accepted (bsm corr w v : Visibility) (σ : EnvironmentState e) :
    (∑ r, ((wernerRound bsm corr).branch (some r)).map
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ.matrix)) =
      isotropic (multiplyVisibility corr (multiplyVisibility bsm (multiplyVisibility w v))) := by
  simp only [wernerRound, preRound_map, trace_tensor_state]
  simpa only [noisyWernerOutput, noisyAccepted, noisyOutcome, isotropic,
    input_density_tensor] using noisy_visibility_matrix bsm corr w v

/-- The second continuation is independent of the first delivered message in this specialization. -/
theorem uniform_continuation {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b₁ c₁ b₂ c₂ fresh : Visibility)
    (σ₂ : EnvironmentState e₂) (r s : BellMeasurement) (o : Outcome) :
    continuation (wernerCascade (e₁ := e₁) b₁ c₁ b₂ c₂ fresh σ₂) r o =
      continuation (wernerCascade (e₁ := e₁) b₁ c₁ b₂ c₂ fresh σ₂) s o := rfl

/-- Exact matrix equality for the actual v4.26 cascade, aggregating all successful histories. -/
theorem cascade_visibility_matrix {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b₁ c₁ b₂ c₂ fresh w v : Visibility)
    (σ₁ : EnvironmentState e₁) (σ₂ : EnvironmentState e₂) :
    acceptedCascade (wernerCascade b₁ c₁ b₂ c₂ fresh σ₂)
        ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix) =
      isotropic (multiplyVisibility c₂ (multiplyVisibility b₂
        (multiplyVisibility
          (multiplyVisibility c₁ (multiplyVisibility b₁ (multiplyVisibility w v))) fresh))) := by
  let C := wernerCascade (e₁ := e₁) b₁ c₁ b₂ c₂ fresh σ₂
  let N := (isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix
  have hc (r : BellMeasurement) (o : Outcome) :
      continuation C r o = continuation C .phiPlus o := rfl
  change acceptedCascade C N = _
  unfold acceptedCascade
  simp only [cascadeBranch, KrausBranch.comp_map, hc]
  rw [Finset.sum_comm]
  have hs (r : BellMeasurement) :
      (∑ s, (continuation C .phiPlus (some r)).map ((C.first.branch (some s)).map N)) =
        (continuation C .phiPlus (some r)).map (∑ s, (C.first.branch (some s)).map N) :=
    (map_sum ((continuation C .phiPlus (some r)).linear) _ _).symm
  simp only [hs]
  have hf : (∑ s, (C.first.branch (some s)).map N) =
      isotropic (multiplyVisibility c₁ (multiplyVisibility b₁ (multiplyVisibility w v))) :=
    wernerRound_accepted b₁ c₁ w v σ₁
  rw [hf]
  simp only [continuation, KrausBranch.comp_map, preparation_map]
  exact wernerRound_accepted b₂ c₂
    (multiplyVisibility c₁ (multiplyVisibility b₁ (multiplyVisibility w v))) fresh σ₂

/-- Under perfect readout the accepted aggregate has probability one, so no conditioning factor. -/
theorem cascade_visibility_trace {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b₁ c₁ b₂ c₂ fresh w v : Visibility)
    (σ₁ : EnvironmentState e₁) (σ₂ : EnvironmentState e₂) :
    (acceptedCascade (wernerCascade b₁ c₁ b₂ c₂ fresh σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix)).trace = 1 := by
  rw [cascade_visibility_matrix, isotropic_trace]

/-- Link the matrix target overlap to the separately proved scalar transition. -/
theorem cascade_fidelity_transition {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b₁ c₁ b₂ c₂ fresh w v : Visibility)
    (σ₁ : EnvironmentState e₁) (σ₂ : EnvironmentState e₂) :
    (targetOverlap (acceptedCascade (wernerCascade b₁ c₁ b₂ c₂ fresh σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix))).re =
      QuantumCascadeReduction.wernerFidelity
        (QuantumCascadeReduction.wernerTransition
          (QuantumCascadeReduction.ofVisibilities b₂ c₂ fresh)
          (c₁.val * b₁.val * w.val * v.val)) := by
  rw [cascade_visibility_matrix]
  simp only [isotropic, density_overlap, isotropicDistribution, multiplyVisibility,
    QuantumCascadeReduction.wernerFidelity, QuantumCascadeReduction.wernerTransition,
    QuantumCascadeReduction.alphaParam, QuantumCascadeReduction.ofVisibilities]
  norm_num
  ring

theorem cascade_fidelity_nonincrease {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b₁ c₁ b₂ c₂ fresh w v : Visibility)
    (σ₁ : EnvironmentState e₁) (σ₂ : EnvironmentState e₂) :
    (targetOverlap (acceptedCascade (wernerCascade b₁ c₁ b₂ c₂ fresh σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix))).re ≤
      QuantumCascadeReduction.wernerFidelity (c₁.val * b₁.val * w.val * v.val) := by
  rw [cascade_fidelity_transition]
  exact QuantumCascadeReduction.fidelity_monotonicity _ _
    (mul_nonneg (mul_nonneg (mul_nonneg c₁.nonnegative b₁.nonnegative) w.nonnegative)
      v.nonnegative)

theorem cascade_visibility_positive {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b₁ c₁ b₂ c₂ fresh w v : Visibility)
    (σ₁ : EnvironmentState e₁) (σ₂ : EnvironmentState e₂) :
    (acceptedCascade (wernerCascade b₁ c₁ b₂ c₂ fresh σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix)).PosSemidef := by
  rw [cascade_visibility_matrix]
  exact density_positive _

structure QuantumWernerCascadeSuite : Prop where
  matrix_formula : ∀ b₁ c₁ b₂ c₂ fresh w v
    (σ₁ : EnvironmentState (Fin 2)) (σ₂ : EnvironmentState (Fin 3)),
    acceptedCascade (wernerCascade b₁ c₁ b₂ c₂ fresh σ₂)
        ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix) =
      isotropic (multiplyVisibility c₂ (multiplyVisibility b₂
        (multiplyVisibility
          (multiplyVisibility c₁ (multiplyVisibility b₁ (multiplyVisibility w v))) fresh)))
  trace_one : ∀ b₁ c₁ b₂ c₂ fresh w v
    (σ₁ : EnvironmentState (Fin 2)) (σ₂ : EnvironmentState (Fin 3)),
    (acceptedCascade (wernerCascade b₁ c₁ b₂ c₂ fresh σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix)).trace = 1
  nonincrease : ∀ b₁ c₁ b₂ c₂ fresh w v
    (σ₁ : EnvironmentState (Fin 2)) (σ₂ : EnvironmentState (Fin 3)),
    (targetOverlap (acceptedCascade (wernerCascade b₁ c₁ b₂ c₂ fresh σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix))).re ≤
      QuantumCascadeReduction.wernerFidelity (c₁.val * b₁.val * w.val * v.val)

theorem verification_suite : QuantumWernerCascadeSuite :=
  ⟨cascade_visibility_matrix, cascade_visibility_trace, cascade_fidelity_nonincrease⟩

end QuantumWernerCascade
