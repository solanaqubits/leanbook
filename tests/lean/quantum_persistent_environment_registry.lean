import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumPersistentEnvironment.QuantumPersistentEnvironmentSuite := r.persistent_environment

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumMemoryCounterexample.QuantumMemoryCounterexampleSuite := r.memory_counterexample

example : QuantumMemoryCounterexample.QuantumMemoryCounterexampleSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.memory_counterexample
