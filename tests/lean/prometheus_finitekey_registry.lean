import Verification.MasterSuite
example : PrometheusNQKDFiniteKey.PrometheusNQKDFiniteKeySuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.nqkd_finitekey
