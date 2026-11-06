/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPostBSMEnvironment

/-! Message-dependent CPTP post-processing of the correlated-input instrument.
Post channels act on AD only, with no subsequent coupling to the retained memory.
The input remains the full joint matrix. Rejection receives no correction noise. -/
noncomputable section
namespace QuantumCorrelatedPostNoise
open QuantumGateNoiseComposition QuantumCorrelatedMemoryBSM QuantumOrderedNoiseComposition
open QuantumBellDiagonalInputs QuantumEntanglementSwappingPurificationContract
open QuantumRectangularSwapping QuantumStateAvailabilityContract QuantumGeneralBellReadout
open QuantumOutcomeInstrument QuantumSwappingInstrument QuantumPersistentEnvironment
open QuantumMixedEnvironment QuantumEnvironmentExtension QuantumCentralDepolarization
open QuantumBellCircuitRefinement QuantumPostBSMEnvironment QuantumTensorStageEnvironment
open scoped BigOperators Matrix Kronecker ComplexOrder

section Generic
variable {n o k j : Type} [Fintype n] [Fintype o] [DecidableEq o]
  [Fintype k] [Fintype j]

/-- Composing a rectangular weighted family with a square CPTP channel. -/
theorem post_weighted_family (E : CPTP o j) (w : k → ℝ) (K : k → Matrix o n ℂ)
    (M : Matrix n n ℂ) :
    E.map (weightedFamily w K M) =
      weightedFamily (fun ij : k × j => w ij.1) (fun ij => E.op ij.2 * K ij.1) M := by
  unfold weightedFamily
  rw [E.map_sum]
  simp only [CPTP.map, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- Arbitrary finite ancillas, not just positivity of the unextended input. -/
theorem post_weighted_cp (E : CPTP o j) (w : k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (K : k → Matrix o n ℂ) : IsCPMap (fun M => E.map (weightedFamily w K M)) := by
  have heq : (fun M => E.map (weightedFamily w K M)) =
      weightedFamily (fun ij : k × j => w ij.1) (fun ij => E.op ij.2 * K ij.1) :=
    funext (post_weighted_family E w K)
  rw [heq]
  exact weightedFamily_cp (fun ij : k × j => w ij.1) (fun ij => hw ij.1)
    (fun ij => E.op ij.2 * K ij.1)

omit [Fintype o] [DecidableEq o] in
/-- Square-root absorption valid for any rectangular input/output dimensions. -/
theorem sqrt_sandwich_rectangular (w : ℝ) (hw : 0 ≤ w) (K : Matrix o n ℂ)
    (M : Matrix n n ℂ) :
    ((Real.sqrt w : ℂ) • K) * M * ((Real.sqrt w : ℂ) • K).conjTranspose =
      (w : ℂ) • (K * M * K.conjTranspose) := by
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt hw]

end Generic

variable {e κ : Type} [Fintype e] [DecidableEq e] [Fintype κ]

/-- The reject branch is the identity linear map; delivered messages select their channel. -/
def postLinear (post : BellMeasurement → CPTP PairIndex κ) :
    Outcome → (PairDensity →ₗ[ℂ] PairDensity)
  | none => LinearMap.id
  | some r => (post r).linear

def noisyJointLinear (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome) :
    JointFourDensity e →ₗ[ℂ] PairDensity :=
  (postLinear post o).comp (reducedJointLinear ss model o)

def noisyJointOutcome (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    (N : JointFourDensity e) : PairDensity := noisyJointLinear ss post model o N

def noisyJointMicro (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (m r : BellMeasurement)
    (N : JointFourDensity e) : PairDensity := (post r).map (reducedJointMicro ss model m r N)

/-- Size 4 by (16 * dim E); the environment selector is already in jointPathBranch. -/
def postPath (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (m r : BellMeasurement)
    (ij : (Paths ss × e) × κ) : Matrix PairIndex (FourIndex × e) ℂ :=
  (post r).op ij.2 * jointPathBranch ss m r ij.1

def microKraus (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (m r : BellMeasurement)
    (ij : (Paths ss × e) × κ) : Matrix PairIndex (FourIndex × e) ℂ :=
  (Real.sqrt (weight model m r) : ℂ) • postPath ss post m r ij

theorem noisy_micro_weighted (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (m r : BellMeasurement)
    (N : JointFourDensity e) :
    noisyJointMicro ss post model m r N =
      weightedFamily (fun _ => weight model m r) (postPath ss post m r) N := by
  unfold noisyJointMicro
  have h : reducedJointMicro ss model m r N =
      weightedFamily (fun _ => weight model m r) (jointPathBranch ss m r) N := by
    rw [reducedJointMicro_kraus, weightedFamily, Finset.smul_sum]
  rw [h, post_weighted_family]
  rfl

theorem noisy_micro_kraus (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (m r : BellMeasurement)
    (N : JointFourDensity e) :
    noisyJointMicro ss post model m r N =
      ∑ ij, microKraus ss post model m r ij * N *
        (microKraus ss post model m r ij).conjTranspose := by
  rw [noisy_micro_weighted]
  simp only [microKraus, sqrt_sandwich_rectangular _ (weight_nonnegative model m r),
    weightedFamily]

theorem noisy_micro_cp (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (m r : BellMeasurement) :
    IsCPMap (noisyJointMicro ss post model m r) := by
  have heq := funext (noisy_micro_weighted ss post model m r)
  rw [heq]
  exact weightedFamily_cp _ (fun _ => weight_nonnegative model m r) _

theorem noisy_micro_trace (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (m r : BellMeasurement)
    (N : JointFourDensity e) :
    (noisyJointMicro ss post model m r N).trace = (reducedJointMicro ss model m r N).trace :=
  (post r).trace _

/-- Independent AD post-processing commutes with discarding the environment. -/
theorem post_before_environment_trace (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (m r : BellMeasurement)
    (N : JointFourDensity e) :
    traceEnvironment ((QuantumDecoupledEnvironment.extendCPTP (post r)).map
      (QuantumMemoryBSM.jointMicro ss model m r N)) = noisyJointMicro ss post model m r N :=
  QuantumDecoupledEnvironment.traceEnvironment_extendCPTP _ _

theorem noisy_outcome_some (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (r : BellMeasurement)
    (N : JointFourDensity e) :
    noisyJointOutcome ss post model (some r) N = ∑ m, noisyJointMicro ss post model m r N := by
  change (post r).map (reducedJointOutcome ss model (some r) N) = _
  rw [reduced_outcome_some, CPTP.map_sum]
  rfl

theorem noisy_outcome_cp (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome) :
    IsCPMap (noisyJointOutcome ss post model o) := by
  cases o with
  | none => exact reducedJointOutcome_cp ss model none
  | some r =>
    change IsCPMap (fun N => (post r).map (reducedJointOutcome ss model (some r) N))
    rw [reducedJointOutcome_family]
    exact post_weighted_cp (post r)
      (fun i : BellMeasurement × (Paths ss × e) => outcomeWeight model (some r) i.1)
      (fun i => outcome_weight_nonnegative model (some r) i.1) (outcomePath ss (some r))

theorem noisy_outcome_positive (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    (N : JointFourDensity e) (hN : N.PosSemidef) :
    (noisyJointOutcome ss post model o N).PosSemidef := by
  cases o with
  | none => exact reducedJointOutcome_positive ss model none N hN
  | some r => exact (post r).positive _ (reducedJointOutcome_positive ss model (some r) N hN)

theorem noisy_outcome_trace (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    (N : JointFourDensity e) :
    (noisyJointOutcome ss post model o N).trace = (reducedJointOutcome ss model o N).trace := by
  cases o with
  | none => rfl
  | some r => exact (post r).trace _

theorem noisy_total_trace (ss : List (Stage (FourIndex × e)))
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (N : JointFourDensity e) :
    (∑ o : Outcome, noisyJointOutcome ss post model o N).trace = N.trace := by
  simp only [Matrix.trace_sum, noisy_outcome_trace]
  rw [← Matrix.trace_sum, reducedJointOutcome_total_trace ss h]

theorem noisy_zero_iff (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    (N : JointFourDensity e) (hN : N.PosSemidef) :
    (noisyJointOutcome ss post model o N).trace.re = 0 ↔ noisyJointOutcome ss post model o N = 0 :=
  QuantumNullConditioning.psd_zero_probability_iff _ (noisy_outcome_positive ss post model o N hN)

/-- A trace-preserving output channel neither creates nor removes zero PSD branches. -/
theorem noisy_zero_iff_original (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    (N : JointFourDensity e) (hN : N.PosSemidef) :
    noisyJointOutcome ss post model o N = 0 ↔ reducedJointOutcome ss model o N = 0 := by
  rw [← noisy_zero_iff ss post model o N hN, noisy_outcome_trace,
    reducedJointOutcome_zero_iff ss model o N hN]

theorem noisy_outcome_sum (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    {a : Type} [Fintype a] (c : a → ℂ) (N : a → JointFourDensity e) :
    noisyJointOutcome ss post model o (∑ i, c i • N i) =
      ∑ i, c i • noisyJointOutcome ss post model o (N i) := by
  change noisyJointLinear ss post model o _ = _
  rw [map_sum]
  simp only [map_smul]
  rfl

theorem identity_post_refinement (ss : List (Stage (FourIndex × e)))
    (model : Readout) (o : Outcome) (N : JointFourDensity e) :
    noisyJointOutcome ss (fun _ => identityChannel PairIndex) model o N =
      reducedJointOutcome ss model o N := by
  cases o with
  | none => rfl
  | some r => exact QuantumGateNoiseComposition.identity_map _

/-- The old mixed-environment bridge is reused without an ideal-analyzer premise. -/
theorem noisy_product_partial_trace (ss : List (Stage (FourIndex × e)))
    (σ : EnvironmentState e) (post : BellMeasurement → CPTP PairIndex κ)
    (model : Readout) (o : Outcome) (M : FourDensity) :
    noisyJointOutcome ss post model o (M ⊗ₖ σ.matrix) =
      postLinear post o (QuantumMixedMemoryBSM.outcome ss σ model o M) := by
  change postLinear post o (reducedJointOutcome ss model o _) = _
  rw [reducedJointOutcome_product]

/-- Linear extension to finite sums of products; coefficients need not be probabilities. -/
theorem noisy_sum_products (ss : List (Stage (FourIndex × e)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    {a : Type} [Fintype a] (c : a → ℂ) (M : a → FourDensity) (σ : a → EnvironmentState e) :
    noisyJointOutcome ss post model o (∑ i, c i • (M i ⊗ₖ (σ i).matrix)) =
      ∑ i, c i • postLinear post o (QuantumMixedMemoryBSM.outcome ss (σ i) model o (M i)) := by
  rw [noisy_outcome_sum]
  simp only [noisy_product_partial_trace]

/-- The 4-by-16 system channel is available for fixed, initially independent environment state. -/
theorem noisy_product_bridge (ss : List (Stage (FourIndex × e)))
    (σ : EnvironmentState e) (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    (M : FourDensity) :
    noisyJointOutcome ss post model o (M ⊗ₖ σ.matrix) =
      noisyOutcome (QuantumMixedMemoryBSM.effectivePre ss σ) post model o M := by
  rw [noisy_product_partial_trace, QuantumMixedMemoryBSM.outcome_bridge ss σ h]
  cases o with
  | none => rfl
  | some r =>
    change (post r).map (∑ m, microMap model m r _) = _
    rw [CPTP.map_sum]
    rfl

/-- Output processing preserves the post-analyzer interaction invariance of v4.23. -/
theorem noisy_post_interaction_invariant (ss : List (Stage (FourIndex × Fin 2)))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    (N : JointFourDensity (Fin 2)) :
    noisyJointOutcome (ss ++ [postStage]) post model o N = noisyJointOutcome ss post model o N := by
  change postLinear post o (reducedJointOutcome _ _ _ _) = postLinear post o _
  rw [post_interaction_outcome_invariant]
  rfl

theorem noisy_tensor_stages_reduction (ss : List (Stage FourIndex × Stage e))
    (post : BellMeasurement → CPTP PairIndex κ) (model : Readout) (o : Outcome)
    (N : JointFourDensity e) :
    noisyJointOutcome (tensorStages ss) post model o N =
      postLinear post o (QuantumMultiStageBSM.outcome (ss.map Prod.fst) model o
        (traceEnvironment N)) := by
  change postLinear post o (reducedJointOutcome _ _ _ _) = _
  rw [tensorStages_outcome_marginal_reduction]

structure QuantumCorrelatedPostNoiseSuite : Prop where
  cp : ∀ (ss : List (Stage (FourIndex × Fin 2)))
    (post : BellMeasurement → CPTP PairIndex (Fin 2)) model o,
    IsCPMap (noisyJointOutcome ss post model o)
  trace : ∀ (ss : List (Stage (FourIndex × Fin 2)))
    (post : BellMeasurement → CPTP PairIndex (Fin 2)) model o N,
    (noisyJointOutcome ss post model o N).trace = (reducedJointOutcome ss model o N).trace
  null : ∀ (ss : List (Stage (FourIndex × Fin 2)))
    (post : BellMeasurement → CPTP PairIndex (Fin 2)) model o N, N.PosSemidef →
    (noisyJointOutcome ss post model o N = 0 ↔ reducedJointOutcome ss model o N = 0)

theorem verification_suite : QuantumCorrelatedPostNoiseSuite :=
  ⟨noisy_outcome_cp, noisy_outcome_trace, noisy_zero_iff_original⟩

end QuantumCorrelatedPostNoise
