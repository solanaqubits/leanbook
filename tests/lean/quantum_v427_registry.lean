import Verification.MasterSuite

example : QuantumCascadeReduction.QuantumCascadeReductionSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.cascade_decay

example : QuantumWernerCascade.QuantumWernerCascadeSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.werner_cascade
