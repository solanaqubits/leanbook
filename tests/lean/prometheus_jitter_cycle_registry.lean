import Verification.MasterSuite
example : PrometheusJitterWindow.PrometheusJitterWindowSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.jitter_window
example : PrometheusRSCycleModel.PrometheusRSCycleModelSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.rs_cycle
