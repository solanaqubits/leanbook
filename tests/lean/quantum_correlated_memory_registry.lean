import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumCorrelatedMemoryBSM.QuantumCorrelatedMemoryBSMSuite := r.correlated_memory_bsm

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumCorrelatedMemoryWitness.QuantumCorrelatedMemoryWitnessSuite :=
  r.correlated_memory_witness

example : QuantumCorrelatedMemoryWitness.QuantumCorrelatedMemoryWitnessSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.correlated_memory_witness
