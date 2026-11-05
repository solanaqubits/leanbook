import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumBinaryMemoryCoupling.QuantumBinaryMemoryCouplingSuite := r.binary_memory_coupling

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumBSMMemoryWitness.QuantumBSMMemoryWitnessSuite := r.bsm_memory_witness

example : QuantumBSMMemoryWitness.QuantumBSMMemoryWitnessSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.bsm_memory_witness
