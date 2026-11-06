import Verification.MasterSuite

example : QuantumDecoupledEnvironment.QuantumDecoupledEnvironmentSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.decoupled_environment

example : QuantumCorrelatedProbabilityWitness.QuantumCorrelatedProbabilityWitnessSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.probability_shift
