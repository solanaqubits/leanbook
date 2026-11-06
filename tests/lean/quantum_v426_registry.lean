import Verification.MasterSuite

example : QuantumCascadedSwapping.QuantumCascadedSwappingSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.cascade
