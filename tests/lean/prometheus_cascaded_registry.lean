import Verification.MasterSuite
open PrometheusCascadedFECBound
example : PrometheusCascadedFECBoundSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.prometheus_cascaded_fec
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusCascadedFECBoundSuite :=
  s.quantum_physics_full_suite.prometheus_cascaded_fec
