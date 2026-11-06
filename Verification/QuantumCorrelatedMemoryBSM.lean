/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumMixedMemoryBSM

/-! Final environment reduction on arbitrary correlated joint inputs.
No preparation or factorization of the input is assumed. -/
noncomputable section
namespace QuantumCorrelatedMemoryBSM
open QuantumBellDiagonalInputs QuantumEntanglementSwappingPurificationContract
open QuantumRectangularSwapping QuantumStateAvailabilityContract
open QuantumGeneralBellReadout QuantumOutcomeInstrument QuantumSwappingInstrument
open QuantumGateNoiseComposition QuantumOrderedNoiseComposition
open QuantumPersistentEnvironment QuantumEnvironmentExtension
open QuantumCentralDepolarization QuantumBellCircuitRefinement QuantumInternalBSMNoise
open QuantumMemoryBSM QuantumMixedEnvironment
open scoped BigOperators ComplexOrder Matrix Kronecker

section Generic
variable {n o k : Type} [Fintype n] [Fintype k]

/-- Block action on a spectator of any finite dimension, with the spectator on the right. -/
def liftMapGen (a : Type) (Φ : Matrix n n ℂ → Matrix o o ℂ)
    (M : Matrix (n × a) (n × a) ℂ) : Matrix (o × a) (o × a) ℂ :=
  fun i j => Φ (Matrix.of fun x y => M (x,i.2) (y,j.2)) i.1 j.1

/-- Complete positivity; linearity is supplied separately by the concrete operator sums. -/
def IsCPMap (Φ : Matrix n n ℂ → Matrix o o ℂ) : Prop :=
  ∀ (a : Type) [Fintype a] [DecidableEq a] (M : Matrix (n × a) (n × a) ℂ),
    M.PosSemidef → (liftMapGen a Φ M).PosSemidef

def weightedFamily (w : k → ℝ) (K : k → Matrix o n ℂ) (M : Matrix n n ℂ) :
    Matrix o o ℂ := ∑ i, (w i : ℂ) • (K i * M * (K i).conjTranspose)

theorem weightedFamily_positive [Finite o] (w : k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (K : k → Matrix o n ℂ) (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    (weightedFamily w K M).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact (hM.mul_mul_conjTranspose_same (K i)).smul (by exact_mod_cast hw i)

theorem lift_weightedFamily (a : Type) [Fintype a] [DecidableEq a]
    (w : k → ℝ) (K : k → Matrix o n ℂ) (M : Matrix (n × a) (n × a) ℂ) :
    liftMapGen a (weightedFamily w K) M =
      weightedFamily w (fun i => K i ⊗ₖ (1 : Matrix a a ℂ)) M := by
  ext i j : 2
  simp [liftMapGen, weightedFamily, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply,
    apply_ite (starRingEnd ℂ), mul_ite]

theorem weightedFamily_cp [Finite o] (w : k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (K : k → Matrix o n ℂ) : IsCPMap (weightedFamily w K) := by
  intro a _ _ M hM
  rw [lift_weightedFamily]
  exact weightedFamily_positive w hw _ M hM

theorem weightedFamily_add (w : k → ℝ) (K : k → Matrix o n ℂ) (M N : Matrix n n ℂ) :
    weightedFamily w K (M + N) = weightedFamily w K M + weightedFamily w K N := by
  simp [weightedFamily, Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]

theorem weightedFamily_smul (w : k → ℝ) (K : k → Matrix o n ℂ) (c : ℂ) (M : Matrix n n ℂ) :
    weightedFamily w K (c • M) = c • weightedFamily w K M := by
  simp only [weightedFamily, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

end Generic

variable {e : Type} [Fintype e] [DecidableEq e]
abbrev JointFourDensity (e : Type) := Matrix (FourIndex × e) (FourIndex × e) ℂ

def reducedJointMicro (ss : List (Stage (FourIndex × e))) (model : Readout)
    (m r : BellMeasurement) (N : JointFourDensity e) : PairDensity :=
  traceEnvironment (jointMicro ss model m r N)

def reducedJointReject (ss : List (Stage (FourIndex × e))) (model : Readout)
    (N : JointFourDensity e) : PairDensity := traceEnvironment (jointReject ss model N)

def reducedJointOutcome (ss : List (Stage (FourIndex × e))) (model : Readout)
    (o : Outcome) (N : JointFourDensity e) : PairDensity :=
  traceEnvironment (jointOutcome ss model o N)

theorem reduced_outcome_some (ss : List (Stage (FourIndex × e))) (model : Readout)
    (r : BellMeasurement) (N : JointFourDensity e) :
    reducedJointOutcome ss model (some r) N = ∑ m, reducedJointMicro ss model m r N := by
  exact trace_environment_sum _

def jointPathReduction (ss : List (Stage (FourIndex × e))) (m : BellMeasurement)
    (pe : Paths ss × e) : Matrix PairIndex (FourIndex × e) ℂ :=
  select (n := PairIndex) pe.2 * jointReduction ss m pe.1

def jointPathBranch (ss : List (Stage (FourIndex × e))) (m r : BellMeasurement)
    (pe : Paths ss × e) : Matrix PairIndex (FourIndex × e) ℂ :=
  select (n := PairIndex) pe.2 * jointBranch ss m r pe.1

theorem joint_family_partial_trace {k : Type} [Fintype k]
    (K : k → Matrix (PairIndex × e) (FourIndex × e) ℂ) (N : JointFourDensity e) :
    traceEnvironment (∑ i, K i * N * (K i).conjTranspose) =
      ∑ pe : k × e, (select (n := PairIndex) pe.2 * K pe.1) * N *
        (select (n := PairIndex) pe.2 * K pe.1).conjTranspose := by
  rw [trace_environment_family]
  simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  exact Finset.sum_comm

theorem reducedJointMicro_kraus (ss : List (Stage (FourIndex × e))) (model : Readout)
    (m r : BellMeasurement) (N : JointFourDensity e) :
    reducedJointMicro ss model m r N = (weight model m r : ℂ) •
      ∑ pe, jointPathBranch ss m r pe * N * (jointPathBranch ss m r pe).conjTranspose := by
  rw [reducedJointMicro, jointMicro, trace_environment_smul, joint_family_partial_trace]
  rfl

theorem reducedJointReject_kraus (ss : List (Stage (FourIndex × e))) (model : Readout)
    (N : JointFourDensity e) :
    reducedJointReject ss model N = ∑ m, ((1 - model.detection m : ℝ) : ℂ) •
      ∑ pe, jointPathReduction ss m pe * N * (jointPathReduction ss m pe).conjTranspose := by
  unfold reducedJointReject jointReject
  rw [trace_environment_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [trace_environment_smul, joint_family_partial_trace]
  rfl

/-- A uniform label space for each of the five outcomes. -/
def outcomeWeight (model : Readout) : Outcome → BellMeasurement → ℝ
  | none, m => 1 - model.detection m
  | some r, m => weight model m r

def outcomePath (ss : List (Stage (FourIndex × e))) :
    Outcome → BellMeasurement × (Paths ss × e) → Matrix PairIndex (FourIndex × e) ℂ
  | none, mpe => jointPathReduction ss mpe.1 mpe.2
  | some r, mpe => jointPathBranch ss mpe.1 r mpe.2

theorem outcome_weight_nonnegative (model : Readout) (o : Outcome) (m : BellMeasurement) :
    0 ≤ outcomeWeight model o m := by
  cases o with
  | none => exact sub_nonneg.mpr (model.detection_le_one m)
  | some r => exact weight_nonnegative model m r

theorem reducedJointOutcome_family (ss : List (Stage (FourIndex × e)))
    (model : Readout) (o : Outcome) :
    reducedJointOutcome ss model o =
      weightedFamily (fun mpe => outcomeWeight model o mpe.1) (outcomePath ss o) := by
  funext N
  cases o with
  | none =>
    change reducedJointReject ss model N = _
    rw [reducedJointReject_kraus]
    simp only [weightedFamily, Fintype.sum_prod_type, outcomeWeight, outcomePath,
      Finset.smul_sum]
  | some r =>
    rw [reduced_outcome_some]
    simp only [reducedJointMicro_kraus, weightedFamily, Fintype.sum_prod_type,
      outcomeWeight, outcomePath, Finset.smul_sum]

theorem reducedJointOutcome_cp (ss : List (Stage (FourIndex × e)))
    (model : Readout) (o : Outcome) : IsCPMap (reducedJointOutcome ss model o) := by
  rw [reducedJointOutcome_family]
  exact weightedFamily_cp
    (fun mpe : BellMeasurement × (Paths ss × e) => outcomeWeight model o mpe.1)
    (fun mpe => outcome_weight_nonnegative model o mpe.1) (outcomePath ss o)

theorem reducedJointOutcome_positive (ss : List (Stage (FourIndex × e)))
    (model : Readout) (o : Outcome) (N : JointFourDensity e) (hN : N.PosSemidef) :
    (reducedJointOutcome ss model o N).PosSemidef := by
  rw [reducedJointOutcome_family]
  exact weightedFamily_positive
    (fun mpe : BellMeasurement × (Paths ss × e) => outcomeWeight model o mpe.1)
    (fun mpe => outcome_weight_nonnegative model o mpe.1) (outcomePath ss o) N hN

theorem reducedJointOutcome_zero_iff (ss : List (Stage (FourIndex × e)))
    (model : Readout) (o : Outcome) (N : JointFourDensity e) (hN : N.PosSemidef) :
    (reducedJointOutcome ss model o N).trace.re = 0 ↔ reducedJointOutcome ss model o N = 0 :=
  QuantumNullConditioning.psd_zero_probability_iff _
    (reducedJointOutcome_positive ss model o N hN)

def reducedJointLinear (ss : List (Stage (FourIndex × e))) (model : Readout) (o : Outcome) :
    JointFourDensity e →ₗ[ℂ] PairDensity where
  toFun := reducedJointOutcome ss model o
  map_add' := by rw [reducedJointOutcome_family]; exact weightedFamily_add _ _
  map_smul' := by rw [reducedJointOutcome_family]; exact weightedFamily_smul _ _

theorem reducedJointOutcome_product (ss : List (Stage (FourIndex × e)))
    (σ : EnvironmentState e) (model : Readout) (o : Outcome) (M : FourDensity) :
    reducedJointOutcome ss model o (M ⊗ₖ σ.matrix) =
      QuantumMixedMemoryBSM.outcome ss σ model o M :=
  QuantumMixedMemoryBSM.outcome_partial_trace ss σ model o M

theorem reducedJointOutcome_sum_products {ι : Type} [Fintype ι]
    (ss : List (Stage (FourIndex × e))) (model : Readout) (o : Outcome)
    (c : ι → ℂ) (M : ι → FourDensity) (σ : ι → EnvironmentState e) :
    reducedJointOutcome ss model o (∑ i, c i • (M i ⊗ₖ (σ i).matrix)) =
      ∑ i, c i • QuantumMixedMemoryBSM.outcome ss (σ i) model o (M i) := by
  change reducedJointLinear ss model o _ = _
  rw [map_sum]
  simp only [map_smul, reducedJointLinear, LinearMap.coe_mk, AddHom.coe_mk,
    reducedJointOutcome_product]

/-- Generalized input-noise refinement; its argument is still the full joint matrix. -/
theorem joint_reduction_effective (ss : List (Stage (FourIndex × e)))
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (m : BellMeasurement)
    (p : Paths ss) : jointReduction ss m p = extend (reduction m) * (effective ss).op p := by
  rw [jointReduction, path_factorization, h, ← Matrix.mul_assoc, extend_mul,
    computational_analysis_reduction]

theorem joint_branch_effective (ss : List (Stage (FourIndex × e)))
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (m r : BellMeasurement)
    (p : Paths ss) : jointBranch ss m r p = extend (branchOperator m r) * (effective ss).op p := by
  rw [jointBranch, joint_reduction_effective ss h, ← Matrix.mul_assoc, extend_mul]
  rfl

theorem reducedJointMicro_effective (ss : List (Stage (FourIndex × e)))
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (model : Readout)
    (m r : BellMeasurement) (N : JointFourDensity e) :
    reducedJointMicro ss model m r N =
      microMap model m r (traceEnvironment ((effective ss).map N)) := by
  have hs : (∑ p, jointBranch ss m r p * N * (jointBranch ss m r p).conjTranspose) =
      extend (branchOperator m r) * (effective ss).map N *
        (extend (branchOperator m r)).conjTranspose := by
    simp only [joint_branch_effective ss h, CPTP.map, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [reducedJointMicro, jointMicro, hs, trace_environment_smul, trace_environment_sandwich]
  rfl

theorem reducedJointReject_effective (ss : List (Stage (FourIndex × e)))
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (model : Readout)
    (N : JointFourDensity e) : reducedJointReject ss model N =
      lostMap model (traceEnvironment ((effective ss).map N)) := by
  have hs (m : BellMeasurement) :
      (∑ p, jointReduction ss m p * N * (jointReduction ss m p).conjTranspose) =
      extend (reduction m) * (effective ss).map N * (extend (reduction m)).conjTranspose := by
    simp only [joint_reduction_effective ss h, CPTP.map, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold reducedJointReject jointReject
  simp only [hs, trace_environment_sum, trace_environment_smul, trace_environment_sandwich]
  rfl

theorem reducedJointOutcome_effective (ss : List (Stage (FourIndex × e)))
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary)) (model : Readout)
    (o : Outcome) (N : JointFourDensity e) : reducedJointOutcome ss model o N =
      outcomeMap model o (traceEnvironment ((effective ss).map N)) := by
  cases o with
  | none => exact reducedJointReject_effective ss h model N
  | some r =>
    rw [reduced_outcome_some]
    simp only [reducedJointMicro_effective ss h, outcomeMap, reportedMap]

theorem reducedJointOutcome_total_trace (ss : List (Stage (FourIndex × e)))
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (model : Readout) (N : JointFourDensity e) :
    (∑ o : Outcome, reducedJointOutcome ss model o N).trace = N.trace := by
  simp only [reducedJointOutcome_effective ss h]
  rw [outcome_total_trace, trace_environment_trace, CPTP.trace]


structure QuantumCorrelatedMemoryBSMSuite : Prop where
  complete_positive : ∀ (ss : List (Stage (FourIndex × Fin 2))) model o,
    IsCPMap (reducedJointOutcome ss model o)
  null_branch : ∀ (ss : List (Stage (FourIndex × Fin 2))) model o N,
    N.PosSemidef → ((reducedJointOutcome ss model o N).trace.re = 0 ↔
      reducedJointOutcome ss model o N = 0)
  trace_balance : ∀ (ss : List (Stage (FourIndex × Fin 2))),
    (ideal ss).matrix = extend (embedBC analysisUnitary) → ∀ model N,
      (∑ o : Outcome, reducedJointOutcome ss model o N).trace = N.trace

theorem verification_suite : QuantumCorrelatedMemoryBSMSuite :=
  ⟨reducedJointOutcome_cp, reducedJointOutcome_zero_iff, reducedJointOutcome_total_trace⟩

end QuantumCorrelatedMemoryBSM
