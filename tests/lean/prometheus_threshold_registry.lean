import Verification.MasterSuite
example : PrometheusThresholdTomography.PrometheusThresholdTomographySuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.threshold_tomography
