/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumBinaryMemoryCoupling
import Verification.QuantumMemoryBSM

/-! An explicit spectator-to-environment CNOT echo inside the Bell analyzer.
Retained and reset environments have identical Bell-message probabilities but
different corrected outer-pair density matrices on two perfect input Bell pairs. -/
noncomputable section
namespace QuantumBSMMemoryWitness
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout QuantumNoisyBellInstrument
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumInternalBSMNoise
open QuantumOrderedNoiseComposition QuantumPersistentEnvironment QuantumEnvironmentExtension
open QuantumMultiStageBSM QuantumBinaryMemoryCoupling QuantumNoisySwapping
open scoped BigOperators ComplexOrder Matrix

/-- The environment records the computational basis value of the outer qubit A. -/
def outerFlag (i : FourIndex) : Bool := decide (i.1.1 = 1)

def echoStages : List (Stage (FourIndex × Bool)) :=
  QuantumMemoryBSM.memoryStages (coupling outerFlag).channel (coupling outerFlag).channel

theorem central_preserves_flag (U : PairDensity) (i j : FourIndex)
    (h : outerFlag i ≠ outerFlag j) : embedBC U i j = 0 := by
  have ha : i.1.1 ≠ j.1.1 := by intro he; apply h; simp [outerFlag, he]
  simp [embedBC, ha]

theorem effective_echo (M : FourDensity) :
    (QuantumMemoryBSM.effectivePre echoStages false).map M = M := by
  rw [QuantumMemoryBSM.effectivePre, reduced_map]
  change traceEnvironment ((effective
    [⟨Unit, inferInstance, extendGate (centralGate cnotGate), (coupling outerFlag).channel⟩,
     ⟨Unit, inferInstance, extendGate (centralGate hGate), (coupling outerFlag).channel⟩]).map
       (prepare false M)) = M
  rw [two_stage_effective]
  have hmat : (gateCompose (extendGate (centralGate hGate))
      (extendGate (centralGate cnotGate))).matrix =
      (extendGate (centralGate analysisGate) : UnitaryGate (FourIndex × Bool)).matrix := by
    change extend (embedBC hGate.matrix) * extend (embedBC cnot) =
      extend (embedBC analysisUnitary)
    rw [extend_mul, h_gate_matrix, embedBC_mul]
    rfl
  have hp (N : Matrix (FourIndex × Bool) (FourIndex × Bool) ℂ) :
      (pullback (gateCompose (extendGate (centralGate hGate))
        (extendGate (centralGate cnotGate))) (coupling outerFlag).channel).map N =
      (coupling outerFlag).channel.map N := by
    simp only [pullback_map, hmat]
    rw [← pullback_map]
    exact pullback_coupling outerFlag (centralGate analysisGate)
      (central_preserves_flag _) N
  rw [hp, pullback_coupling outerFlag (centralGate cnotGate) (central_preserves_flag _),
    coupling_twice, trace_environment_prepare]

def retainedOutcome (model : Readout) (o : Outcome) (M : FourDensity) : PairDensity :=
  QuantumMemoryBSM.outcome echoStages false model o M

theorem retained_outcome (model : Readout) (o : Outcome) (M : FourDensity) :
    retainedOutcome model o M = outcomeMap model o M := by
  have hi : (ideal echoStages).matrix = extend (embedBC analysisUnitary) :=
    QuantumMemoryBSM.memory_ideal _ _
  rw [retainedOutcome, QuantumMemoryBSM.outcome_bridge echoStages false hi, effective_echo]

/-- Direct computational measurement, followed by the reported Pauli correction. -/
def computationalBranch (m r : BellMeasurement) : BranchMatrix :=
  correction r * computationalReduction m

def computationalOutcome (model : Readout) : Outcome → FourDensity → PairDensity
  | none => fun N => ∑ m, (1 - model.detection m) •
      (computationalReduction m * N * (computationalReduction m).conjTranspose)
  | some r => fun N => ∑ m, weight model m r •
      (computationalBranch m r * N * (computationalBranch m r).conjTranspose)

theorem computational_branch_analysis (m r : BellMeasurement) :
    computationalBranch m r * embedBC analysisUnitary = branchOperator m r := by
  rw [computationalBranch, Matrix.mul_assoc, computational_analysis_reduction, branchOperator]

theorem readout_after_analysis (model : Readout) (o : Outcome) (M : FourDensity) :
    computationalOutcome model o
      (embedBC analysisUnitary * M * (embedBC analysisUnitary).conjTranspose) =
    outcomeMap model o M := by
  have h (L : BranchMatrix) :
      L * (embedBC analysisUnitary * M * (embedBC analysisUnitary).conjTranspose) *
        L.conjTranspose = (L * embedBC analysisUnitary) * M *
          (L * embedBC analysisUnitary).conjTranspose := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  cases o <;> simp only [computationalOutcome, outcomeMap, h, computational_analysis_reduction,
    computational_branch_analysis, lostMap, reportedMap, microMap]

/-- A physical reset discards the first environment and prepares false before stage two. -/
def resetOutcome (model : Readout) (o : Outcome) (M : FourDensity) : PairDensity :=
  computationalOutcome model o (resetRun echoStages false M)

theorem reset_evolution (M : FourDensity) :
    resetRun echoStages false M = embedBC analysisUnitary *
      dephase outerFlag M * (embedBC analysisUnitary).conjTranspose := by
  unfold echoStages QuantumMemoryBSM.memoryStages
  rw [reset_run_cons, reset_run_cons, reset_run_nil]
  change (reduced (noisyGate (extendGate (centralGate hGate)) (coupling outerFlag).channel)
    false).map ((reduced (noisyGate (extendGate (centralGate cnotGate))
      (coupling outerFlag).channel) false).map M) = _
  rw [reduced_noisy_coupling, reduced_noisy_coupling]
  change dephase outerFlag (embedBC hGate.matrix *
    dephase outerFlag (embedBC cnot * M * (embedBC cnot).conjTranspose) *
      (embedBC hGate.matrix).conjTranspose) = _
  rw [dephase_sandwich outerFlag _ _ (central_preserves_flag _), dephase_idempotent,
    dephase_sandwich outerFlag _ _ (central_preserves_flag _)]
  have hm : embedBC hGate.matrix * embedBC cnot = embedBC analysisUnitary := by
    rw [h_gate_matrix, embedBC_mul]; rfl
  calc
    _ = (embedBC hGate.matrix * embedBC cnot) * dephase outerFlag M *
        (embedBC hGate.matrix * embedBC cnot).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hm]

theorem reset_outcome (model : Readout) (o : Outcome) (M : FourDensity) :
    resetOutcome model o M = outcomeMap model o (dephase outerFlag M) := by
  rw [resetOutcome, reset_evolution, readout_after_analysis]

/-- The actual input is two independent perfect Bell pairs. -/
def input : FourDensity := productDensity .phiPlus .phiPlus

theorem input_valid : input.PosSemidef ∧ input.trace = 1 := by
  constructor
  · exact Matrix.posSemidef_vecMulVec_self_star _
  · rw [input, product_density_tensor, Matrix.trace_kronecker,
      bell_projector_trace]
    norm_num

-- Sixteen A/B basis cases; C/D indices remain symbolic.
theorem dephased_input : dephase outerFlag input =
    (1/2 : ℝ) • productDensity .phiPlus .phiPlus +
    (1/2 : ℝ) • productDensity .phiMinus .phiPlus := by
  ext i j : 2
  rcases i with ⟨⟨a,b⟩,⟨c,d⟩⟩; rcases j with ⟨⟨a',b'⟩,⟨c',d'⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [dephase, outerFlag, input, productDensity, productKet, bellKet,
      Matrix.vecMulVec, Complex.real_smul]
  all_goals split_ifs <;> simp_all <;> ring

theorem perfect_report_matrix (r : BellMeasurement) (M : FourDensity) :
    outcomeMap QuantumBellDiagonalSwapping.perfectReadout (some r) M =
      branchOperator r r * M * (branchOperator r r).conjTranspose := by
  simp [outcomeMap, reportedMap, microMap, weight, QuantumBellDiagonalSwapping.perfectReadout]

theorem perfect_report_product (a b r : BellMeasurement) :
    outcomeMap QuantumBellDiagonalSwapping.perfectReadout (some r) (productDensity a b) =
      (1/4 : ℝ) • bellProjector (bellXor a b) := by
  rw [perfect_report_matrix, component_refinement, xor_cancel]

def mixedOuter : PairDensity :=
  (1/2 : ℝ) • bellProjector .phiPlus + (1/2 : ℝ) • bellProjector .phiMinus

theorem retained_branch (r : BellMeasurement) :
    retainedOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input =
      (1/4 : ℝ) • bellProjector .phiPlus := by
  rw [retained_outcome, input, perfect_report_product]
  rfl

theorem reset_branch (r : BellMeasurement) :
    resetOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input =
      (1/4 : ℝ) • mixedOuter := by
  rw [reset_outcome, dephased_input, perfect_report_matrix]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    component_refinement, xor_cancel, mixedOuter, smul_add, smul_smul]
  norm_num [bellXor, fromBits, xBit, zBit]

theorem mixed_outer_valid : mixedOuter.PosSemidef ∧ mixedOuter.trace = 1 := by
  constructor
  · exact ((Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0:ℝ) ≤ 1/2)).add
      ((Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0:ℝ) ≤ 1/2))
  · simp [mixedOuter, Matrix.trace_add, Matrix.trace_smul, bell_projector_trace]
    norm_num

/-- Identical detector statistics do not imply identical corrected output states. -/
theorem same_report_probabilities (r : BellMeasurement) :
    (retainedOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input).trace.re = 1/4 ∧
    (resetOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input).trace.re = 1/4 := by
  rw [retained_branch, reset_branch]
  simp [Matrix.trace_smul, bell_projector_trace, mixed_outer_valid.2]

def retainedOutput : PairDensity :=
  ∑ r, retainedOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input

def resetOutput : PairDensity :=
  ∑ r, resetOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input

theorem retained_output : retainedOutput = bellProjector .phiPlus := by
  unfold retainedOutput
  simp only [retained_branch, sum_bell, ← add_smul]
  norm_num

theorem reset_output : resetOutput = mixedOuter := by
  unfold resetOutput
  simp only [reset_branch, sum_bell, ← add_smul]
  norm_num

theorem outputs_normalized : retainedOutput.trace = 1 ∧ resetOutput.trace = 1 := by
  rw [retained_output, reset_output, bell_projector_trace, mixed_outer_valid.2]
  exact ⟨rfl,rfl⟩

theorem outputs_positive : retainedOutput.PosSemidef ∧ resetOutput.PosSemidef := by
  rw [retained_output, reset_output]
  exact ⟨Matrix.posSemidef_vecMulVec_self_star _, mixed_outer_valid.1⟩

theorem rejection_absent :
    retainedOutcome QuantumBellDiagonalSwapping.perfectReadout none input = 0 ∧
    resetOutcome QuantumBellDiagonalSwapping.perfectReadout none input = 0 := by
  rw [retained_outcome, reset_outcome]
  simp [outcomeMap, lostMap, QuantumBellDiagonalSwapping.perfectReadout]

theorem output_fidelity_gap : targetOverlap retainedOutput = 1 ∧
    targetOverlap resetOutput = (1/2 : ℂ) := by
  rw [retained_output, reset_output]
  simp [mixedOuter, targetOverlap_add,
    targetOverlap_real_smul,
    QuantumBellDiagonalSwapping.projector_overlap]

theorem output_coherence_gap : retainedOutput (0,0) (1,1) = (1/2 : ℂ) ∧
    resetOutput (0,0) (1,1) = 0 := by
  rw [retained_output, reset_output]
  norm_num [mixedOuter, bellProjector, purePairDensity, Matrix.vecMulVec, bellKet,
    Complex.real_smul, ← pow_two, bellCoeff_sq]

theorem outputs_distinct : retainedOutput ≠ resetOutput := by
  intro h
  have he := congrArg targetOverlap h
  rw [output_fidelity_gap.1, output_fidelity_gap.2] at he
  norm_num at he

structure QuantumBSMMemoryWitnessSuite : Prop where
  input_physical : input.PosSemidef ∧ input.trace = 1
  probabilities : ∀ r,
    (retainedOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input).trace.re = 1/4 ∧
    (resetOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input).trace.re = 1/4
  fidelity_gap : targetOverlap retainedOutput = 1 ∧ targetOverlap resetOutput = (1/2 : ℂ)
  different_outputs : retainedOutput ≠ resetOutput

theorem verification_suite : QuantumBSMMemoryWitnessSuite :=
  ⟨input_valid, same_report_probabilities, output_fidelity_gap, outputs_distinct⟩

end QuantumBSMMemoryWitness
