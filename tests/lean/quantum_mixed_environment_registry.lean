import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumMixedEnvironment.QuantumMixedEnvironmentSuite := r.mixed_environment

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumMixedMemoryBSM.QuantumMixedMemoryBSMSuite := r.mixed_memory_bsm

example : QuantumMixedMemoryBSM.QuantumMixedMemoryBSMSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.mixed_memory_bsm
