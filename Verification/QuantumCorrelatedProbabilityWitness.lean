/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCorrelatedMemoryWitness
import Verification.QuantumDecoupledEnvironment

/-! Same system and environment marginals, but different physical BSM probabilities.
The fixed coupling and its pre-analyzer placement are reused unchanged from v4.21. -/
noncomputable section
namespace QuantumCorrelatedProbabilityWitness
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout QuantumNoisyBellInstrument
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumPersistentEnvironment QuantumEnvironmentExtension QuantumCorrelatedMemoryBSM
open QuantumCorrelatedMemoryWitness QuantumBellDiagonalSwapping
open scoped BigOperators ComplexOrder Matrix Kronecker

/-- GHZ and the same ket with the B bit flipped. -/
def probabilityKet (b : Fin 2) : FourKet :=
  fun a x c d => ghzKet a (if b = 0 then x else 1 - x) c d

def probabilityInput (b : Fin 2) : FourDensity := pureFourDensity (probabilityKet b)

theorem probability_input_zero : probabilityInput 0 = ghzState.matrix := by
  rfl

theorem probability_input_positive (b : Fin 2) : (probabilityInput b).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem probability_input_trace (b : Fin 2) : (probabilityInput b).trace = 1 := by
  fin_cases b <;>
    norm_num [probabilityInput, probabilityKet, pureFourDensity, flattenFour, ghzKet,
      Matrix.trace, Matrix.diag, Matrix.vecMulVec, Fintype.sum_prod_type,
      Fin.sum_univ_two, ← pow_two, bellCoeff_sq]

set_option maxHeartbeats 1000000 in
-- Eight binary index cases check a sparse permutation without an external evaluator.
/-- The controlled bit flip exchanges the two GHZ-parity inputs exactly when q=1. -/
theorem coupling_probability_prepared (q b : Fin 2) :
    coupling.channel.map (prepare q (probabilityInput b)) =
      prepare q (probabilityInput (if q = 0 then b else 1 - b)) := by
  ext i j : 2
  rw [coupling_entry]
  rcases i with ⟨⟨⟨a,x⟩,cd⟩,u⟩
  rcases j with ⟨⟨⟨a',x'⟩,cd'⟩,v⟩
  fin_cases q <;> fin_cases b <;> fin_cases u <;> fin_cases v <;>
    fin_cases a <;> fin_cases x <;> fin_cases a' <;> fin_cases x' <;>
    simp [flipEB, prepare_entry, probabilityInput, probabilityKet, pureFourDensity,
      flattenFour, ghzKet, Matrix.vecMulVec]

/-- Complex traces, not only their real parts, for all four physical measurement outcomes. -/
theorem probability_input_branch_trace (b : Fin 2) (m : BellMeasurement) :
    (reduction m * probabilityInput b * (reduction m).conjTranspose).trace =
      (if (m = .phiPlus ∨ m = .phiMinus) then
        (if b = 0 then 1/2 else 0) else (if b = 0 then 0 else 1/2) : ℂ) := by
  rw [probabilityInput, pureFourDensity, sandwich_pure, reduction_amplitudes]
  change (purePairDensity (readoutBranch m (probabilityKet b))).trace = _
  rw [pure_pair_trace, branch_equals_bell_contraction]
  fin_cases b <;> cases m <;>
    norm_num [probabilityKet, pairNormSq, swappingContraction, ghzKet, bellKet,
      Fin.sum_univ_two, ← pow_two, bellCoeff_sq] <;> decide

def probWitnessPlus : JointFourDensity (Fin 2) :=
  (1/2 : ℂ) • prepare 0 (probabilityInput 0) +
    (1/2 : ℂ) • prepare 1 (probabilityInput 1)

def probWitnessMinus : JointFourDensity (Fin 2) :=
  (1/2 : ℂ) • prepare 1 (probabilityInput 0) +
    (1/2 : ℂ) • prepare 0 (probabilityInput 1)

theorem probWitnessPlus_valid : probWitnessPlus.PosSemidef ∧ probWitnessPlus.trace = 1 := by
  constructor
  · exact ((prepare_positive 0 _ (probability_input_positive 0)).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2)).add
      ((prepare_positive 1 _ (probability_input_positive 1)).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2))
  · simp [probWitnessPlus, Matrix.trace_add, Matrix.trace_smul, prepare_trace,
      probability_input_trace]
    norm_num

theorem probWitnessMinus_valid : probWitnessMinus.PosSemidef ∧ probWitnessMinus.trace = 1 := by
  constructor
  · exact ((prepare_positive 1 _ (probability_input_positive 0)).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2)).add
      ((prepare_positive 0 _ (probability_input_positive 1)).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2))
  · simp [probWitnessMinus, Matrix.trace_add, Matrix.trace_smul, prepare_trace,
      probability_input_trace]
    norm_num

theorem probWitness_same_system_marginal :
    traceEnvironment probWitnessPlus = traceEnvironment probWitnessMinus := by
  simp [probWitnessPlus, probWitnessMinus, trace_environment_add, trace_environment_smul,
    trace_environment_prepare]

theorem probWitness_same_environment_marginal :
    traceSystem probWitnessPlus = traceSystem probWitnessMinus := by
  ext i j : 2
  change (∑ k, probWitnessPlus (k,i) (k,j)) = ∑ k, probWitnessMinus (k,i) (k,j)
  simp only [probWitnessPlus, probWitnessMinus, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  change (1/2 : ℂ) * traceSystem (prepare 0 (probabilityInput 0)) i j +
    (1/2 : ℂ) * traceSystem (prepare 1 (probabilityInput 1)) i j =
    (1/2 : ℂ) * traceSystem (prepare 1 (probabilityInput 0)) i j +
    (1/2 : ℂ) * traceSystem (prepare 0 (probabilityInput 1)) i j
  simp only [trace_system_prepared, probability_input_trace]
  exact add_comm _ _

theorem probWitness_marginals_and_validity :
    probWitnessPlus.PosSemidef ∧ probWitnessPlus.trace = 1 ∧
    probWitnessMinus.PosSemidef ∧ probWitnessMinus.trace = 1 ∧
    traceEnvironment probWitnessPlus = traceEnvironment probWitnessMinus ∧
    traceSystem probWitnessPlus = traceSystem probWitnessMinus :=
  ⟨probWitnessPlus_valid.1, probWitnessPlus_valid.2, probWitnessMinus_valid.1,
    probWitnessMinus_valid.2, probWitness_same_system_marginal,
    probWitness_same_environment_marginal⟩

theorem probability_reduced_plus :
    traceEnvironment (coupling.channel.map probWitnessPlus) = probabilityInput 0 := by
  simp only [probWitnessPlus, CPTP.map_add, CPTP.map_smul, coupling_probability_prepared]
  norm_num only
  rw [trace_environment_add]
  simp only [trace_environment_smul, trace_environment_prepare]
  norm_num
  rw [← add_smul]
  norm_num

theorem probability_reduced_minus :
    traceEnvironment (coupling.channel.map probWitnessMinus) = probabilityInput 1 := by
  simp only [probWitnessMinus, CPTP.map_add, CPTP.map_smul, coupling_probability_prepared]
  norm_num only
  rw [trace_environment_add]
  simp only [trace_environment_smul, trace_environment_prepare]
  norm_num
  rw [← add_smul]
  norm_num

theorem perfect_branch_trace (r : BellMeasurement) (M : FourDensity) :
    (outcomeMap perfectReadout (some r) M).trace =
      (reduction r * M * (reduction r).conjTranspose).trace := by
  rw [QuantumBSMMemoryWitness.perfect_report_matrix, sandwich_trace, branch_effect,
    ← reduction_effect, ← sandwich_trace]

theorem probWitness_branch_traces (r : BellMeasurement) :
    (reducedJointOutcome witnessStages perfectReadout (some r) probWitnessPlus).trace =
      (if r = .phiPlus ∨ r = .phiMinus then 1/2 else 0 : ℂ) ∧
    (reducedJointOutcome witnessStages perfectReadout (some r) probWitnessMinus).trace =
      (if r = .phiPlus ∨ r = .phiMinus then 0 else 1/2 : ℂ) := by
  simp only [reducedJointOutcome_effective _ witness_ideal, witness_effective,
    probability_reduced_plus, probability_reduced_minus, perfect_branch_trace,
    probability_input_branch_trace]
  norm_num

theorem probWitness_phiPlus_branch_trace_shift :
    (reducedJointOutcome witnessStages perfectReadout (some .phiPlus) probWitnessPlus).trace =
      (1/2 : ℂ) ∧
    (reducedJointOutcome witnessStages perfectReadout
      (some .phiPlus) probWitnessMinus).trace = 0 := by
  simpa using probWitness_branch_traces .phiPlus

theorem probWitness_phiPlus_minus_zero :
    reducedJointOutcome witnessStages perfectReadout (some .phiPlus) probWitnessMinus = 0 := by
  apply (reducedJointOutcome_zero_iff _ _ _ _ probWitnessMinus_valid.1).mp
  rw [probWitness_phiPlus_branch_trace_shift.2]
  rfl

theorem no_marginal_only_branch_probability_phiPlus :
    ¬ ∃ f : FourDensity → ℂ, ∀ N : JointFourDensity (Fin 2),
      N.PosSemidef → N.trace = 1 → f (traceEnvironment N) =
        (reducedJointOutcome witnessStages perfectReadout (some .phiPlus) N).trace := by
  rintro ⟨f,hf⟩
  have hp := hf probWitnessPlus probWitnessPlus_valid.1 probWitnessPlus_valid.2
  have hm := hf probWitnessMinus probWitnessMinus_valid.1 probWitnessMinus_valid.2
  rw [probWitness_same_system_marginal] at hp
  have h := hp.symm.trans hm
  rw [probWitness_phiPlus_branch_trace_shift.1, probWitness_phiPlus_branch_trace_shift.2] at h
  norm_num at h

structure QuantumCorrelatedProbabilityWitnessSuite : Prop where
  valid_plus : probWitnessPlus.PosSemidef ∧ probWitnessPlus.trace = 1
  valid_minus : probWitnessMinus.PosSemidef ∧ probWitnessMinus.trace = 1
  same_system : traceEnvironment probWitnessPlus = traceEnvironment probWitnessMinus
  same_environment : traceSystem probWitnessPlus = traceSystem probWitnessMinus
  probability_shift :
    (reducedJointOutcome witnessStages perfectReadout (some .phiPlus) probWitnessPlus).trace =
      (1/2 : ℂ) ∧
    (reducedJointOutcome witnessStages perfectReadout (some .phiPlus) probWitnessMinus).trace = 0
  obstruction : ¬ ∃ f : FourDensity → ℂ, ∀ N : JointFourDensity (Fin 2),
    N.PosSemidef → N.trace = 1 → f (traceEnvironment N) =
      (reducedJointOutcome witnessStages perfectReadout (some .phiPlus) N).trace

theorem verification_suite : QuantumCorrelatedProbabilityWitnessSuite :=
  ⟨probWitnessPlus_valid, probWitnessMinus_valid, probWitness_same_system_marginal,
    probWitness_same_environment_marginal, probWitness_phiPlus_branch_trace_shift,
    no_marginal_only_branch_probability_phiPlus⟩

end QuantumCorrelatedProbabilityWitness
