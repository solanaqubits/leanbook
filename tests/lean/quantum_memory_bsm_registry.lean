import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumEnvironmentExtension.QuantumEnvironmentExtensionSuite := r.environment_extension

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumMemoryBSM.QuantumMemoryBSMSuite := r.memory_bsm

example : QuantumMemoryBSM.QuantumMemoryBSMSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.memory_bsm
