/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCorrelatedPostNoise

/-! Two rounds with classical feedback, a fresh pair and fresh second-round memory.
All instrument maps are unnormalized. Conditional normalization is separate.
The first environment is discarded and is not reused in the second round. -/
noncomputable section
namespace QuantumCascadedSwapping
open QuantumCorrelatedPostNoise QuantumCorrelatedMemoryBSM QuantumMixedEnvironment
open QuantumGateNoiseComposition QuantumOrderedNoiseComposition QuantumGeneralBellReadout
open QuantumBellDiagonalInputs QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumOutcomeInstrument QuantumEnvironmentExtension
open QuantumCentralDepolarization QuantumBellCircuitRefinement QuantumNullConditioning
open scoped BigOperators ComplexOrder Matrix Kronecker

/-- A finite rectangular Kraus family. Completeness is a property of an instrument sum. -/
structure KrausBranch (n m : Type) where
  labels : Type
  finiteLabels : Fintype labels
  op : labels → Matrix m n ℂ

attribute [instance] KrausBranch.finiteLabels

namespace KrausBranch
variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

def map (K : KrausBranch n m) (M : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ k, K.op k * M * (K.op k).conjTranspose

def linear (K : KrausBranch n m) : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun := K.map
  map_add' M N := by simp [map, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c M := by simp [map, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

omit [Fintype p] [Fintype m] in
theorem cp [Finite m] (K : KrausBranch n m) : IsCPMap K.map := by
  have h : K.map = weightedFamily (fun _ : K.labels => (1 : ℝ)) K.op := by
    funext M
    simp [map, weightedFamily]
  rw [h]
  exact weightedFamily_cp _ (fun _ => by norm_num) _

omit [Fintype p] [Fintype m] in
theorem positive [Finite m] (K : KrausBranch n m) (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    (K.map M).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro k _
  exact hM.mul_mul_conjTranspose_same _

/-- The order is output family after input family. -/
def comp (L : KrausBranch m p) (K : KrausBranch n m) : KrausBranch n p where
  labels := L.labels × K.labels
  finiteLabels := inferInstance
  op jk := L.op jk.1 * K.op jk.2

omit [Fintype p] in
theorem comp_map (L : KrausBranch m p) (K : KrausBranch n m) (M : Matrix n n ℂ) :
    (L.comp K).map M = L.map (K.map M) := by
  change (∑ jk : L.labels × K.labels,
    (L.op jk.1 * K.op jk.2) * M * (L.op jk.1 * K.op jk.2).conjTranspose) = _
  simp only [map, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

end KrausBranch

/-- Preparation has output dimension dim(n) * dim(e), not an extra system label. -/
def preparation {n e : Type} [Fintype e] [DecidableEq e] [DecidableEq n]
    (σ : EnvironmentState e) : KrausBranch n (n × e) where
  labels := e
  finiteLabels := inferInstance
  op := prepareOp σ

theorem preparation_map {n e : Type} [Fintype n] [DecidableEq n]
    [Fintype e] [DecidableEq e] (σ : EnvironmentState e) (M : Matrix n n ℂ) :
    (preparation σ).map M = M ⊗ₖ σ.matrix := preparation_semantics σ M

theorem preparation_trace {n e : Type} [Fintype n] [DecidableEq n]
    [Fintype e] [DecidableEq e] (σ : EnvironmentState e) (M : Matrix n n ℂ) :
    ((preparation σ).map M).trace = M.trace := by
  rw [preparation_map, Matrix.trace_kronecker, σ.trace_one, mul_one]

/-- A round includes the analyzer premise needed by the inherited five-outcome balance. -/
structure Round (e κ : Type) [Fintype e] [DecidableEq e] [Fintype κ] where
  stages : List (Stage (FourIndex × e))
  analyzer : (ideal stages).matrix = extend (embedBC analysisUnitary)
  post : BellMeasurement → CPTP PairIndex κ
  readout : Readout

namespace Round
variable {e κ : Type} [Fintype e] [DecidableEq e] [Fintype κ]

def branch (R : Round e κ) : Outcome → KrausBranch (FourIndex × e) PairIndex
  | none =>
    { labels := BellMeasurement × (Paths R.stages × e)
      finiteLabels := inferInstance
      op := fun i => (Real.sqrt (outcomeWeight R.readout none i.1) : ℂ) •
        outcomePath R.stages none i }
  | some r =>
    { labels := BellMeasurement × ((Paths R.stages × e) × κ)
      finiteLabels := inferInstance
      op := fun i => microKraus R.stages R.post R.readout i.1 r i.2 }

theorem branch_map (R : Round e κ) (o : Outcome) (N : JointFourDensity e) :
    (R.branch o).map N = noisyJointOutcome R.stages R.post R.readout o N := by
  cases o with
  | none =>
    change _ = reducedJointOutcome R.stages R.readout none N
    rw [reducedJointOutcome_family]
    simp only [KrausBranch.map, branch, weightedFamily,
      sqrt_sandwich_rectangular _ (outcome_weight_nonnegative R.readout none _)]
    rfl
  | some r =>
    rw [noisy_outcome_some]
    change (∑ i : BellMeasurement × ((Paths R.stages × e) × κ),
      microKraus R.stages R.post R.readout i.1 r i.2 * N *
        (microKraus R.stages R.post R.readout i.1 r i.2).conjTranspose) = _
    simp only [Fintype.sum_prod_type, QuantumCorrelatedPostNoise.noisy_micro_kraus]

theorem total_trace (R : Round e κ) (N : JointFourDensity e) :
    (∑ o : Outcome, ((R.branch o).map N).trace) = N.trace := by
  simp only [branch_map, ← Matrix.trace_sum]
  exact QuantumCorrelatedPostNoise.noisy_total_trace R.stages R.analyzer R.post R.readout N

end Round

/-- Only the delivered first message chooses the second instrument and fixed fresh resources. -/
structure Cascade (e₁ e₂ κ₁ κ₂ : Type) [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] [Fintype κ₁] [Fintype κ₂] where
  first : Round e₁ κ₁
  second : BellMeasurement → Round e₂ κ₂
  freshPair : BellMeasurement → EnvironmentState PairIndex
  freshMemory : BellMeasurement → EnvironmentState e₂

/-- One early rejection, or a delivered first message and any second outcome. -/
abbrev TerminalOutcome := Option (BellMeasurement × Outcome)

theorem terminal_outcome_card : Fintype.card TerminalOutcome = 21 := by decide

variable {e₁ e₂ κ₁ κ₂ : Type} [Fintype e₁] [DecidableEq e₁]
  [Fintype e₂] [DecidableEq e₂] [Fintype κ₁] [Fintype κ₂]

/-- A 4-by-4 input first receives a fresh pair, then independent second-round memory. -/
def continuation (C : Cascade e₁ e₂ κ₁ κ₂) (r : BellMeasurement) (o : Outcome) :
    KrausBranch PairIndex PairIndex :=
  ((C.second r).branch o).comp
    ((preparation (C.freshMemory r)).comp (preparation (C.freshPair r)))

def cascadeBranch (C : Cascade e₁ e₂ κ₁ κ₂) (r : BellMeasurement) (o : Outcome) :
    KrausBranch (FourIndex × e₁) PairIndex :=
  (continuation C r o).comp (C.first.branch (some r))

def terminalBranch (C : Cascade e₁ e₂ κ₁ κ₂) :
    TerminalOutcome → KrausBranch (FourIndex × e₁) PairIndex
  | none => C.first.branch none
  | some (r, o) => cascadeBranch C r o

/-- Exact bridge to v4.24, on the full correlated first input and independent fresh resources. -/
theorem continuation_semantics (C : Cascade e₁ e₂ κ₁ κ₂)
    (r : BellMeasurement) (o : Outcome) (M : PairDensity) :
    (continuation C r o).map M =
      noisyJointOutcome (C.second r).stages (C.second r).post (C.second r).readout o
        ((M ⊗ₖ (C.freshPair r).matrix) ⊗ₖ (C.freshMemory r).matrix) := by
  simp only [continuation, KrausBranch.comp_map, preparation_map, Round.branch_map]

theorem cascade_semantics (C : Cascade e₁ e₂ κ₁ κ₂)
    (r : BellMeasurement) (o : Outcome) (N : JointFourDensity e₁) :
    (cascadeBranch C r o).map N = (continuation C r o).map
      (noisyJointOutcome C.first.stages C.first.post C.first.readout (some r) N) := by
  rw [cascadeBranch, KrausBranch.comp_map, Round.branch_map]

/-- Explicit composed rectangular operators include both preparations between the rounds. -/
theorem cascade_kraus (C : Cascade e₁ e₂ κ₁ κ₂)
    (r : BellMeasurement) (o : Outcome) (N : JointFourDensity e₁) :
    (cascadeBranch C r o).map N =
      ∑ l : ((C.second r).branch o).labels, ∑ q : e₂, ∑ t : PairIndex,
      ∑ k : (C.first.branch (some r)).labels,
        (((C.second r).branch o).op l * prepareOp (n := FourIndex) (C.freshMemory r) q *
          prepareOp (n := PairIndex) (C.freshPair r) t * (C.first.branch (some r)).op k) * N *
        (((C.second r).branch o).op l * prepareOp (n := FourIndex) (C.freshMemory r) q *
          prepareOp (n := PairIndex) (C.freshPair r) t *
          (C.first.branch (some r)).op k).conjTranspose := by
  unfold cascadeBranch continuation
  simp only [KrausBranch.comp_map]
  simp only [KrausBranch.map, preparation, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem terminal_cp (C : Cascade e₁ e₂ κ₁ κ₂) (o : TerminalOutcome) :
    IsCPMap (terminalBranch C o).map := (terminalBranch C o).cp

theorem terminal_positive (C : Cascade e₁ e₂ κ₁ κ₂) (o : TerminalOutcome)
    (N : JointFourDensity e₁) (hN : N.PosSemidef) :
    ((terminalBranch C o).map N).PosSemidef := (terminalBranch C o).positive N hN

theorem terminal_sum (C : Cascade e₁ e₂ κ₁ κ₂) (o : TerminalOutcome)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (N : ι → JointFourDensity e₁) :
    (terminalBranch C o).map (∑ i, c i • N i) =
      ∑ i, c i • (terminalBranch C o).map (N i) := by
  exact map_sum ((terminalBranch C o).linear) _ _ |>.trans
    (Finset.sum_congr rfl fun i _ => map_smul ((terminalBranch C o).linear) _ _)

theorem continuation_total_trace (C : Cascade e₁ e₂ κ₁ κ₂)
    (r : BellMeasurement) (M : PairDensity) :
    (∑ o : Outcome, ((continuation C r o).map M).trace) = M.trace := by
  simp only [continuation, KrausBranch.comp_map]
  rw [Round.total_trace, preparation_trace, preparation_trace]

theorem terminal_total_trace (C : Cascade e₁ e₂ κ₁ κ₂) (N : JointFourDensity e₁) :
    (∑ o : TerminalOutcome, ((terminalBranch C o).map N).trace) = N.trace := by
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type, terminalBranch,
    cascadeBranch, KrausBranch.comp_map, continuation_total_trace]
  simpa only [Fintype.sum_option] using C.first.total_trace N

/-- Conditional continuation is not a linear or CP map of the original input. -/
def conditionalContinuation (C : Cascade e₁ e₂ κ₁ κ₂)
    (r : BellMeasurement) (o : Outcome) (N : JointFourDensity e₁) : PairDensity :=
  (continuation C r o).map (normalizeOrZero ((C.first.branch (some r)).map N))

/-- Reconstruction remains valid even when the first probability is zero. -/
theorem cascade_reconstruction (C : Cascade e₁ e₂ κ₁ κ₂)
    (r : BellMeasurement) (o : Outcome) (N : JointFourDensity e₁) (hN : N.PosSemidef) :
    (cascadeBranch C r o).map N =
      ((C.first.branch (some r)).map N).trace.re • conditionalContinuation C r o N := by
  rw [cascadeBranch, KrausBranch.comp_map]
  have h := normalize_reconstruct _ ((C.first.branch (some r)).positive N hN)
  have hh := congrArg (continuation C r o).map h
  have hs := (continuation C r o).linear.restrictScalars ℝ |>.map_smul
    ((C.first.branch (some r)).map N).trace.re
    (normalizeOrZero ((C.first.branch (some r)).map N))
  exact hh.symm.trans hs

/-- The second factor is evaluated on the normalized first output, not the original input. -/
theorem cascade_probability_factorization (C : Cascade e₁ e₂ κ₁ κ₂)
    (r : BellMeasurement) (o : Outcome) (N : JointFourDensity e₁) (hN : N.PosSemidef) :
    ((cascadeBranch C r o).map N).trace.re =
      ((C.first.branch (some r)).map N).trace.re * (conditionalContinuation C r o N).trace.re := by
  rw [cascade_reconstruction C r o N hN, Matrix.trace_smul]
  simp

theorem zero_first_branch_gives_zero_continuation (C : Cascade e₁ e₂ κ₁ κ₂)
    (r : BellMeasurement) (o : Outcome) (N : JointFourDensity e₁) (hN : N.PosSemidef)
    (hz : ((C.first.branch (some r)).map N).trace.re = 0) :
    (cascadeBranch C r o).map N = 0 := by
  rw [cascade_reconstruction C r o N hN, hz, zero_smul]

/-- At positive first probability the conditional second instrument is normalized. -/
theorem conditional_total_trace (C : Cascade e₁ e₂ κ₁ κ₂)
    (r : BellMeasurement) (N : JointFourDensity e₁) (hN : N.PosSemidef)
    (hp : 0 < ((C.first.branch (some r)).map N).trace.re) :
    (∑ o : Outcome, (conditionalContinuation C r o N).trace) = 1 := by
  unfold conditionalContinuation
  rw [continuation_total_trace]
  exact normalize_trace_one _ ((C.first.branch (some r)).positive N hN) hp

theorem terminal_probability_nonnegative (C : Cascade e₁ e₂ κ₁ κ₂)
    (o : TerminalOutcome) (N : JointFourDensity e₁) (hN : N.PosSemidef) :
    0 ≤ ((terminalBranch C o).map N).trace.re :=
  (Complex.nonneg_iff.mp (terminal_positive C o N hN).trace_nonneg).1

theorem terminal_probabilities_sum_one (C : Cascade e₁ e₂ κ₁ κ₂)
    (N : JointFourDensity e₁) (htrace : N.trace = 1) :
    (∑ o : TerminalOutcome, ((terminalBranch C o).map N).trace.re) = 1 := by
  rw [← Complex.re_sum, terminal_total_trace, htrace]
  rfl

structure QuantumCascadedSwappingSuite : Prop where
  count : Fintype.card TerminalOutcome = 21
  cp : ∀ (C : Cascade (Fin 2) (Fin 3) Unit Unit) o,
    IsCPMap (terminalBranch C o).map
  balance : ∀ (C : Cascade (Fin 2) (Fin 3) Unit Unit) N,
    (∑ o : TerminalOutcome, ((terminalBranch C o).map N).trace) = N.trace
  zero : ∀ (C : Cascade (Fin 2) (Fin 3) Unit Unit) r o N, N.PosSemidef →
    ((C.first.branch (some r)).map N).trace.re = 0 → (cascadeBranch C r o).map N = 0

theorem verification_suite : QuantumCascadedSwappingSuite :=
  ⟨terminal_outcome_card, terminal_cp, terminal_total_trace,
    zero_first_branch_gives_zero_continuation⟩

end QuantumCascadedSwapping
