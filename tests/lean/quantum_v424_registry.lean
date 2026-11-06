import Verification.MasterSuite

example : QuantumCorrelatedPostNoise.QuantumCorrelatedPostNoiseSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.correlated_post
