import Verification.MasterSuite
example : PrometheusMultiLaneQueue.PrometheusMultiLaneQueueSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.prometheus_multilane
example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    PrometheusLifetimeIdentifiability.PrometheusLifetimeIdentifiabilitySuite :=
  s.quantum_physics_full_suite.prometheus_id
