/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCorrelatedMemoryBSM
import Verification.QuantumBSMMemoryWitness

/-! Two joint densities with identical system and environment marginals but
orthogonal corrected Bell outputs under one fixed interaction. -/
noncomputable section
namespace QuantumCorrelatedMemoryWitness
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout QuantumNoisyBellInstrument
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumInternalBSMNoise
open QuantumOrderedNoiseComposition QuantumPersistentEnvironment QuantumEnvironmentExtension
open QuantumMultiStageBSM QuantumNoisyVisibility QuantumMemoryBSM QuantumMixedEnvironment
open QuantumCorrelatedMemoryBSM QuantumNoisySwapping
open scoped BigOperators ComplexOrder Matrix Kronecker

/-- Flip B iff the environment is |1>; all other computational indices are retained. -/
def flipEB (i : FourIndex × Fin 2) : FourIndex × Fin 2 :=
  if i.2 = 0 then i else (((i.1.1.1, 1 - i.1.1.2), i.1.2), i.2)

theorem flipEB_involutive (i : FourIndex × Fin 2) : flipEB (flipEB i) = i := by
  rcases i with ⟨⟨⟨a,b⟩,cd⟩,q⟩
  fin_cases q <;> fin_cases b <;> simp [flipEB]

theorem flipEB_eq_iff (i j : FourIndex × Fin 2) : flipEB i = j ↔ i = flipEB j := by
  constructor
  · intro h; rw [← h, flipEB_involutive]
  · intro h; rw [h, flipEB_involutive]

def couplingMatrix : Matrix (FourIndex × Fin 2) (FourIndex × Fin 2) ℂ :=
  fun i j => if flipEB i = j then 1 else 0

theorem coupling_left (M : JointFourDensity (Fin 2)) (i j) :
    (couplingMatrix * M) i j = M (flipEB i) j := by
  simp [couplingMatrix, Matrix.mul_apply]

theorem coupling_right (M : JointFourDensity (Fin 2)) (i j) :
    (M * couplingMatrix) i j = M i (flipEB j) := by
  simp [couplingMatrix, Matrix.mul_apply, flipEB_eq_iff]

theorem coupling_adjoint : couplingMatrix.conjTranspose = couplingMatrix := by
  ext i j : 2
  have h : flipEB j = i ↔ flipEB i = j := by rw [flipEB_eq_iff]; exact eq_comm
  simp only [couplingMatrix, Matrix.conjTranspose_apply, h]
  split_ifs <;> simp

theorem coupling_squared : couplingMatrix * couplingMatrix = 1 := by
  ext i j : 2
  rw [coupling_left]
  simp [couplingMatrix, flipEB_involutive, Matrix.one_apply]

def coupling : UnitaryGate (FourIndex × Fin 2) :=
  ⟨couplingMatrix, by rw [coupling_adjoint, coupling_squared],
    by rw [coupling_adjoint, coupling_squared]⟩

theorem coupling_entry (N : JointFourDensity (Fin 2)) (i j) :
    coupling.channel.map N i j = N (flipEB i) (flipEB j) := by
  rw [unitary_channel_map]
  change (couplingMatrix * N * couplingMatrix.conjTranspose) i j = _
  rw [coupling_adjoint, coupling_right, coupling_left]

/-- Separate initial noise stage: memoryStages places its noise AFTER each ideal gate. -/
def witnessStages : List (Stage (FourIndex × Fin 2)) :=
  ⟨Unit, inferInstance, identityGate _, coupling.channel⟩ ::
    memoryStages (identityChannel _) (identityChannel _)

theorem witness_ideal :
    (ideal witnessStages).matrix = extend (embedBC analysisUnitary) := by
  change (ideal (memoryStages (identityChannel _) (identityChannel _))).matrix * 1 = _
  rw [Matrix.mul_one, memory_ideal]

theorem effective_identity_memory (N : JointFourDensity (Fin 2)) :
    (effective (memoryStages (identityChannel _) (identityChannel _))).map N = N := by
  have hid (U : UnitaryGate (FourIndex × Fin 2)) (M : JointFourDensity (Fin 2)) :
      (pullback U (identityChannel _)).map M = M := by
    rw [pullback_map, identity_map]
    calc
      _ = (U.matrix.conjTranspose * U.matrix) * M *
          (U.matrix.conjTranspose * U.matrix) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [U.left]; simp
  rw [memoryStages, two_stage_effective, hid, hid]

theorem witness_effective (N : JointFourDensity (Fin 2)) :
    (effective witnessStages).map N = coupling.channel.map N := by
  change (pullback (identityGate _) (compose
    (effective (memoryStages (identityChannel _) (identityChannel _))) coupling.channel)).map N = _
  rw [pullback_map, compose_map, effective_identity_memory]
  simp [identityGate]

def input (b : Fin 2) : FourDensity :=
  productDensity (if b = 0 then .phiPlus else .psiPlus) .phiPlus

theorem input_positive (b : Fin 2) : (input b).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem input_trace (b : Fin 2) : (input b).trace = 1 := by
  simp [input, product_density_tensor, Matrix.trace_kronecker, bell_projector_trace]

set_option maxHeartbeats 1000000 in
-- Enumerating eight binary indices verifies the sparse permutation without numeric oracles.
/-- Exact action on each of the four components of the correlated mixtures. -/
theorem coupling_prepared (q b : Fin 2) :
    coupling.channel.map (prepare q (input b)) =
      prepare q (input (if q = 0 then b else 1 - b)) := by
  ext i j : 2
  rw [coupling_entry]
  rcases i with ⟨⟨⟨a,x⟩,cd⟩,u⟩
  rcases j with ⟨⟨⟨a',x'⟩,cd'⟩,v⟩
  fin_cases q <;> fin_cases b <;> fin_cases u <;> fin_cases v <;>
    fin_cases a <;> fin_cases x <;> fin_cases a' <;> fin_cases x' <;>
    simp [flipEB, prepare_entry, input, product_density_tensor,
      bellProjector, purePairDensity, bellKet, Matrix.vecMulVec]

def witnessPlus : JointFourDensity (Fin 2) :=
  (1/2 : ℂ) • prepare 0 (input 0) + (1/2 : ℂ) • prepare 1 (input 1)

def witnessMinus : JointFourDensity (Fin 2) :=
  (1/2 : ℂ) • prepare 1 (input 0) + (1/2 : ℂ) • prepare 0 (input 1)

theorem witnessPlus_posSemidef_and_trace_one :
    witnessPlus.PosSemidef ∧ witnessPlus.trace = 1 := by
  constructor
  · exact ((prepare_positive 0 _ (input_positive 0)).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2)).add
      ((prepare_positive 1 _ (input_positive 1)).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2))
  · simp [witnessPlus, Matrix.trace_add, Matrix.trace_smul, prepare_trace, input_trace]
    norm_num

theorem witnessMinus_posSemidef_and_trace_one :
    witnessMinus.PosSemidef ∧ witnessMinus.trace = 1 := by
  constructor
  · exact ((prepare_positive 1 _ (input_positive 0)).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2)).add
      ((prepare_positive 0 _ (input_positive 1)).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2))
  · simp [witnessMinus, Matrix.trace_add, Matrix.trace_smul, prepare_trace, input_trace]
    norm_num

theorem trace_environment_add (N M : JointFourDensity (Fin 2)) :
    traceEnvironment (N + M) = traceEnvironment N + traceEnvironment M := by
  ext i j : 2
  simp [traceEnvironment, Finset.sum_add_distrib]

theorem witness_same_system_marginal :
    traceEnvironment witnessPlus = traceEnvironment witnessMinus := by
  simp [witnessPlus, witnessMinus, trace_environment_add, trace_environment_smul,
    trace_environment_prepare]

def traceSystem (N : JointFourDensity (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun q r => ∑ i : FourIndex, N (i,q) (i,r)

theorem trace_system_prepared (q : Fin 2) (M : FourDensity) (i j : Fin 2) :
    traceSystem (prepare q M) i j = if i = q ∧ j = q then M.trace else 0 := by
  simp [traceSystem, prepare_entry, Matrix.trace, Matrix.diag, Finset.sum_ite_irrel]

theorem witness_same_environment_marginal : traceSystem witnessPlus = traceSystem witnessMinus := by
  ext i j : 2
  change (∑ k, witnessPlus (k,i) (k,j)) = ∑ k, witnessMinus (k,i) (k,j)
  simp only [witnessPlus, witnessMinus, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  change (1/2 : ℂ) * traceSystem (prepare 0 (input 0)) i j +
    (1/2 : ℂ) * traceSystem (prepare 1 (input 1)) i j =
    (1/2 : ℂ) * traceSystem (prepare 1 (input 0)) i j +
    (1/2 : ℂ) * traceSystem (prepare 0 (input 1)) i j
  simp only [trace_system_prepared, input_trace]
  exact add_comm _ _

theorem witness_reduced_plus : traceEnvironment (coupling.channel.map witnessPlus) = input 0 := by
  simp only [witnessPlus, CPTP.map_add, CPTP.map_smul, coupling_prepared]
  norm_num only
  rw [trace_environment_add]
  simp only [trace_environment_smul, trace_environment_prepare]
  norm_num
  rw [← add_smul]
  norm_num

theorem witness_reduced_minus : traceEnvironment (coupling.channel.map witnessMinus) = input 1 := by
  simp only [witnessMinus, CPTP.map_add, CPTP.map_smul, coupling_prepared]
  norm_num only
  rw [trace_environment_add]
  simp only [trace_environment_smul, trace_environment_prepare]
  norm_num
  rw [← add_smul]
  norm_num

theorem witness_branch_plus (r : BellMeasurement) :
    reducedJointOutcome witnessStages
      QuantumBellDiagonalSwapping.perfectReadout (some r) witnessPlus =
      (1/4 : ℝ) • bellProjector .phiPlus := by
  rw [reducedJointOutcome_effective _ witness_ideal, witness_effective, witness_reduced_plus]
  exact QuantumBSMMemoryWitness.perfect_report_product .phiPlus .phiPlus r

theorem witness_branch_minus (r : BellMeasurement) :
    reducedJointOutcome witnessStages
      QuantumBellDiagonalSwapping.perfectReadout (some r) witnessMinus =
      (1/4 : ℝ) • bellProjector .psiPlus := by
  rw [reducedJointOutcome_effective _ witness_ideal, witness_effective, witness_reduced_minus]
  exact QuantumBSMMemoryWitness.perfect_report_product .psiPlus .phiPlus r

theorem scaled_bell_distinct :
    (1/4 : ℝ) • bellProjector .phiPlus ≠ (1/4 : ℝ) • bellProjector .psiPlus := by
  intro h
  have he := congrArg (fun M : PairDensity => M (0,0) (0,0)) h
  norm_num [bellProjector, purePairDensity, bellKet, Matrix.vecMulVec, Complex.real_smul,
    ← pow_two, bellCoeff_sq] at he

theorem witness_same_branch_trace_but_diff_branch_matrix (r : BellMeasurement) :
    let outPlus := reducedJointOutcome witnessStages
      QuantumBellDiagonalSwapping.perfectReadout (some r) witnessPlus
    let outMinus := reducedJointOutcome witnessStages
      QuantumBellDiagonalSwapping.perfectReadout (some r) witnessMinus
    outPlus.trace = (1/4 : ℂ) ∧ outMinus.trace = (1/4 : ℂ) ∧ outPlus ≠ outMinus := by
  dsimp only
  rw [witness_branch_plus, witness_branch_minus]
  exact ⟨by simp [Matrix.trace_smul, bell_projector_trace],
    by simp [Matrix.trace_smul, bell_projector_trace], scaled_bell_distinct⟩

theorem no_marginal_only_map_for_witness_config (r : BellMeasurement) :
    ¬ ∃ f : FourDensity → PairDensity, ∀ N : JointFourDensity (Fin 2),
      N.PosSemidef → N.trace = 1 → f (traceEnvironment N) =
        reducedJointOutcome witnessStages
          QuantumBellDiagonalSwapping.perfectReadout (some r) N := by
  rintro ⟨f, hf⟩
  have hp := hf witnessPlus witnessPlus_posSemidef_and_trace_one.1
    witnessPlus_posSemidef_and_trace_one.2
  have hm := hf witnessMinus witnessMinus_posSemidef_and_trace_one.1
    witnessMinus_posSemidef_and_trace_one.2
  rw [witness_same_system_marginal] at hp
  exact (witness_same_branch_trace_but_diff_branch_matrix r).2.2 (hp.symm.trans hm)


def accepted (N : JointFourDensity (Fin 2)) : PairDensity :=
  ∑ r, reducedJointOutcome witnessStages QuantumBellDiagonalSwapping.perfectReadout (some r) N

theorem accepted_plus : accepted witnessPlus = bellProjector .phiPlus := by
  simp only [accepted, witness_branch_plus, sum_bell, ← add_smul]
  norm_num

theorem accepted_minus : accepted witnessMinus = bellProjector .psiPlus := by
  simp only [accepted, witness_branch_minus, sum_bell, ← add_smul]
  norm_num

theorem accepted_fidelity_gap :
    targetOverlap (accepted witnessPlus) = 1 ∧ targetOverlap (accepted witnessMinus) = 0 := by
  rw [accepted_plus, accepted_minus]
  simp [QuantumBellDiagonalSwapping.projector_overlap]

theorem witness_accepted_outputs_distinct : accepted witnessPlus ≠ accepted witnessMinus := by
  intro h
  have hh := congrArg targetOverlap h
  rw [accepted_fidelity_gap.1, accepted_fidelity_gap.2] at hh
  norm_num at hh

structure QuantumCorrelatedMemoryWitnessSuite : Prop where
  positive_plus : witnessPlus.PosSemidef ∧ witnessPlus.trace = 1
  positive_minus : witnessMinus.PosSemidef ∧ witnessMinus.trace = 1
  same_system : traceEnvironment witnessPlus = traceEnvironment witnessMinus
  same_environment : traceSystem witnessPlus = traceSystem witnessMinus
  outputs_differ : accepted witnessPlus ≠ accepted witnessMinus
  obstruction : ∀ r : BellMeasurement,
    ¬ ∃ f : FourDensity → PairDensity, ∀ N : JointFourDensity (Fin 2),
      N.PosSemidef → N.trace = 1 → f (traceEnvironment N) =
        reducedJointOutcome witnessStages QuantumBellDiagonalSwapping.perfectReadout (some r) N

theorem verification_suite : QuantumCorrelatedMemoryWitnessSuite :=
  ⟨witnessPlus_posSemidef_and_trace_one, witnessMinus_posSemidef_and_trace_one,
    witness_same_system_marginal, witness_same_environment_marginal,
    witness_accepted_outputs_distinct, no_marginal_only_map_for_witness_config⟩

end QuantumCorrelatedMemoryWitness
