import Verification.QuantumCorrelatedProbabilityWitness

noncomputable section
open QuantumCorrelatedProbabilityWitness QuantumCorrelatedMemoryWitness
open QuantumCorrelatedMemoryBSM QuantumPersistentEnvironment QuantumBellDiagonalSwapping
open QuantumRectangularSwapping QuantumStateAvailabilityContract
open scoped BigOperators ComplexOrder

example : probWitnessPlus.PosSemidef ∧ probWitnessPlus.trace = 1 ∧
    probWitnessMinus.PosSemidef ∧ probWitnessMinus.trace = 1 ∧
    traceEnvironment probWitnessPlus = traceEnvironment probWitnessMinus ∧
    traceSystem probWitnessPlus = traceSystem probWitnessMinus :=
  probWitness_marginals_and_validity

example : (reducedJointOutcome witnessStages perfectReadout (some .phiPlus)
    probWitnessPlus).trace = (1/2 : ℂ) ∧
    (reducedJointOutcome witnessStages perfectReadout (some .phiPlus) probWitnessMinus).trace = 0 :=
  probWitness_phiPlus_branch_trace_shift

example : (reducedJointOutcome witnessStages perfectReadout (some .psiPlus)
    probWitnessPlus).trace = 0 ∧
    (reducedJointOutcome witnessStages perfectReadout (some .psiPlus)
      probWitnessMinus).trace = (1/2 : ℂ) := by
  simpa using probWitness_branch_traces .psiPlus

example : reducedJointOutcome witnessStages perfectReadout (some .phiPlus) probWitnessMinus = 0 :=
  probWitness_phiPlus_minus_zero

example : ¬ ∃ f : FourDensity → ℂ, ∀ N : JointFourDensity (Fin 2),
    N.PosSemidef → N.trace = 1 → f (traceEnvironment N) =
      (reducedJointOutcome witnessStages perfectReadout (some .phiPlus) N).trace :=
  no_marginal_only_branch_probability_phiPlus
