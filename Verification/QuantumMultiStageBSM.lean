/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumOrderedNoiseComposition
import Verification.QuantumInternalBSMNoise

/-! Direct multi-stage Bell instrumentation and its ordered effective input channel.
The concrete analyzer has independent noise after CNOT and after Hadamard. -/
noncomputable section
namespace QuantumMultiStageBSM
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumInternalBSMNoise
open QuantumOrderedNoiseComposition QuantumLocalPostNoise QuantumNoisyVisibility
open QuantumLocalNoisySwapping
open scoped BigOperators ComplexOrder Matrix

def pathReduction (ss : List (Stage FourIndex)) (m : BellMeasurement) (p : Paths ss) :
    BranchMatrix := computationalReduction m * (direct ss).op p

def pathBranch (ss : List (Stage FourIndex)) (m r : BellMeasurement) (p : Paths ss) :
    BranchMatrix := correction r * pathReduction ss m p

theorem path_reduction_bridge (ss : List (Stage FourIndex))
    (h : (ideal ss).matrix = embedBC analysisUnitary) (m : BellMeasurement) (p : Paths ss) :
    pathReduction ss m p = reduction m * (effective ss).op p := by
  rw [pathReduction, path_factorization, h, ← Matrix.mul_assoc,
    computational_analysis_reduction]

theorem path_branch_bridge (ss : List (Stage FourIndex))
    (h : (ideal ss).matrix = embedBC analysisUnitary) (m r : BellMeasurement) (p : Paths ss) :
    pathBranch ss m r p = branchOperator m r * (effective ss).op p := by
  rw [pathBranch, path_reduction_bridge ss h, ← Matrix.mul_assoc, branchOperator]

def micro (ss : List (Stage FourIndex)) (model : Readout) (m r : BellMeasurement)
    (M : FourDensity) : PairDensity := weight model m r • familyMap (pathBranch ss m r) M

def reject (ss : List (Stage FourIndex)) (model : Readout) (M : FourDensity) : PairDensity :=
  ∑ m, (1 - model.detection m) • familyMap (pathReduction ss m) M

def outcome (ss : List (Stage FourIndex)) (model : Readout) : Outcome → FourDensity → PairDensity
  | none => reject ss model
  | some r => fun M => ∑ m, micro ss model m r M

theorem micro_bridge (ss : List (Stage FourIndex))
    (h : (ideal ss).matrix = embedBC analysisUnitary)
    (model : Readout) (m r : BellMeasurement) (M : FourDensity) :
    micro ss model m r M = microMap model m r ((effective ss).map M) := by
  simp only [micro, familyMap, path_branch_bridge ss h, microMap, CPTP.map,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem reject_bridge (ss : List (Stage FourIndex))
    (h : (ideal ss).matrix = embedBC analysisUnitary)
    (model : Readout) (M : FourDensity) :
    reject ss model M = lostMap model ((effective ss).map M) := by
  simp only [reject, familyMap, path_reduction_bridge ss h, lostMap, CPTP.map,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem outcome_bridge (ss : List (Stage FourIndex))
    (h : (ideal ss).matrix = embedBC analysisUnitary)
    (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome ss model o M = outcomeMap model o ((effective ss).map M) := by
  cases o <;> simp only [outcome, outcomeMap, reject_bridge ss h, micro_bridge ss h, reportedMap]

theorem outcome_noisy_bridge (ss : List (Stage FourIndex))
    (h : (ideal ss).matrix = embedBC analysisUnitary) (model : Readout) (o : Outcome) :
    outcome ss model o =
      noisyOutcome (effective ss) (fun _ => identityChannel PairIndex) model o := by
  funext M
  rw [outcome_bridge ss h]
  cases o <;> simp [noisyOutcome, noisyReject, noisyReported, noisyMicro, outcomeMap, reportedMap]

theorem outcome_cp (ss : List (Stage FourIndex))
    (h : (ideal ss).matrix = embedBC analysisUnitary)
    (model : Readout) (o : Outcome) : IsCP (outcome ss model o) := by
  rw [outcome_noisy_bridge ss h]
  exact noisy_outcome_cp _ _ _ _

theorem total_trace (ss : List (Stage FourIndex))
    (h : (ideal ss).matrix = embedBC analysisUnitary)
    (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, outcome ss model o M).trace = M.trace := by
  simp only [outcome_bridge ss h]
  rw [outcome_total_trace, CPTP.trace]

/-- The remaining gate is obtained from known unitaries and identified with H on B. -/
def hGate : UnitaryGate PairIndex := gateCompose analysisGate cnotGate.inverse

theorem h_gate_matrix : hGate.matrix = hadamardControl := by
  change analysisUnitary * cnot.conjTranspose = _
  rw [cnot_adjoint, analysisUnitary, Matrix.mul_assoc, cnot_squared, Matrix.mul_one]

variable {κ ι : Type} [Fintype κ] [Fintype ι]

def bsmStages (E : CPTP FourIndex κ) (F : CPTP FourIndex ι) : List (Stage FourIndex) :=
  [⟨κ, inferInstance, centralGate cnotGate, E⟩, ⟨ι, inferInstance, centralGate hGate, F⟩]

theorem bsm_ideal (E : CPTP FourIndex κ) (F : CPTP FourIndex ι) :
    (ideal (bsmStages E F)).matrix = embedBC analysisUnitary := by
  change (1 * embedBC hGate.matrix) * embedBC cnot = _
  rw [Matrix.one_mul, h_gate_matrix, embedBC_mul]
  rfl

/-- Explicit chronological density evolution with both internal errors. -/
theorem bsm_run (E : CPTP FourIndex κ) (F : CPTP FourIndex ι) (M : FourDensity) :
    run (bsmStages E F) M =
      F.map (embedBC hadamardControl *
        E.map (embedBC cnot * M * (embedBC cnot).conjTranspose) *
        (embedBC hadamardControl).conjTranspose) := by
  simp only [bsmStages, run, centralGate, cnotGate, h_gate_matrix]

theorem bsm_outcome_bridge (E : CPTP FourIndex κ) (F : CPTP FourIndex ι)
    (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome (bsmStages E F) model o M =
      outcomeMap model o ((effective (bsmStages E F)).map M) :=
  outcome_bridge _ (bsm_ideal E F) model o M

theorem bsm_effective_order (E : CPTP FourIndex κ) (F : CPTP FourIndex ι) (M : FourDensity) :
    (effective (bsmStages E F)).map M =
      (pullback (centralGate analysisGate) F).map
        ((pullback (centralGate cnotGate) E).map M) := by
  rw [bsmStages, two_stage_effective]
  have hmat : (gateCompose (centralGate hGate) (centralGate cnotGate)).matrix =
      (centralGate analysisGate).matrix := by
    change embedBC hGate.matrix * embedBC cnot = embedBC analysisUnitary
    rw [h_gate_matrix, embedBC_mul]
    rfl
  simp only [pullback_map, hmat]

/-- The two isotropic errors combine by multiplication of their visibility parameters. -/
theorem depolarizing_compose (g h : Visibility) (M : PairDensity) :
    (depolarizing h).map ((depolarizing g).map M) =
      (depolarizing (multiplyVisibility h g)).map M := by
  rw [depolarizing_map, CPTP.trace, depolarizing_map, depolarizing_map]
  ext i j : 2
  simp [Matrix.one_apply, multiplyVisibility]
  split_ifs <;> ring

theorem central_composition (E : CPTP PairIndex κ) (F : CPTP PairIndex ι) (M : FourDensity) :
    (centralChannel F).map ((centralChannel E).map M) =
      (centralChannel (compose F E)).map M := by
  rw [← compose_map]
  simp only [CPTP.map, compose, centralChannel, embedBC_mul]

theorem two_depolarizing_effective (g h : Visibility) (M : FourDensity) :
    (effective (bsmStages (centralChannel (depolarizing g))
      (centralChannel (depolarizing h)))).map M =
      (centralChannel (depolarizing (multiplyVisibility h g))).map M := by
  rw [bsm_effective_order, central_depolarizing_transport, central_depolarizing_transport,
    central_composition]
  ext i j : 2
  rw [central_map, central_map, compose_map, depolarizing_compose]

def accepted (ss : List (Stage FourIndex)) (post : BellMeasurement → CPTP PairIndex κ)
    (model : Readout) (M : FourDensity) : PairDensity :=
  ∑ r, (post r).map (outcome ss model (some r) M)

theorem accepted_bridge (ss : List (Stage FourIndex))
    (h : (ideal ss).matrix = embedBC analysisUnitary) (post : BellMeasurement → CPTP PairIndex κ)
    (model : Readout) (M : FourDensity) :
    accepted ss post model M = noisyAccepted (effective ss) post model M := by
  simp only [accepted, outcome, micro_bridge ss h, CPTP.map_sum,
    noisyAccepted, noisyReported, noisyMicro]

theorem two_noise_local_visibility (g h corr w v : Visibility) :
    accepted (bsmStages (centralChannel (depolarizing g)) (centralChannel (depolarizing h)))
      (fun _ => localDepolarizing corr) QuantumBellDiagonalSwapping.perfectReadout
      (inputDensity
        (QuantumBellDiagonalSwapping.isotropicDistribution w.val ⟨w.nonnegative,w.le_one⟩)
        (QuantumBellDiagonalSwapping.isotropicDistribution v.val ⟨v.nonnegative,v.le_one⟩)) =
      isotropic (multiplyVisibility corr
        (multiplyVisibility (multiplyVisibility h g) (multiplyVisibility w v))) := by
  rw [accepted_bridge _ (bsm_ideal _ _)]
  simp only [noisyAccepted, noisyReported, noisyMicro, two_depolarizing_effective]
  exact local_noisy_visibility_matrix (multiplyVisibility h g) corr w v

/-- Reset to a fixed basis state is CPTP; two different resets do not commute. -/
def resetOperator (t j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun a b => if a = t ∧ b = j then 1 else 0

def reset (t : Fin 2) : CPTP (Fin 2) (Fin 2) where
  op := resetOperator t
  complete := by
    ext a b : 2
    simp only [Matrix.sum_apply]
    fin_cases t <;> fin_cases a <;> fin_cases b <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, resetOperator]

def qubitZero : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal fun i => if i = 0 then 1 else 0

theorem qubit_zero_valid : qubitZero.PosSemidef ∧ qubitZero.trace = 1 := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ if i = 0 then (1 : ℂ) else 0
    split_ifs <;> positivity
  · norm_num [qubitZero, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Final |1> probability is 1 for reset0→reset1 and 0 in the reversed order. -/
theorem reset_order_changes_probability :
    (compose (reset 1) (reset 0)).map qubitZero 1 1 = 1 ∧
    (compose (reset 0) (reset 1)).map qubitZero 1 1 = 0 := by
  rw [compose_map, compose_map]
  simp [CPTP.map, reset, resetOperator, qubitZero, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

structure QuantumMultiStageBSMSuite : Prop where
  refinement : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
    (E : CPTP FourIndex κ) (F : CPTP FourIndex ι) model o M,
    outcome (bsmStages E F) model o M = outcomeMap model o ((effective (bsmStages E F)).map M)
  trace_balance : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
    (E : CPTP FourIndex κ) (F : CPTP FourIndex ι) model M,
    (∑ o : Outcome, outcome (bsmStages E F) model o M).trace = M.trace
  order_boundary : (compose (reset 1) (reset 0)).map qubitZero 1 1 = 1 ∧
    (compose (reset 0) (reset 1)).map qubitZero 1 1 = 0

theorem verification_suite : QuantumMultiStageBSMSuite :=
  ⟨bsm_outcome_bridge, fun E F => total_trace _ (bsm_ideal E F), reset_order_changes_probability⟩

end QuantumMultiStageBSM
