import Verification.MasterSuite

example : PrometheusNoiseAudit.PrometheusNoiseAuditSuite :=
  (MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}).quantum_suite.prometheus_noise_audit
example : PrometheusUCNAudit.PrometheusUCNAuditSuite :=
  (MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}).quantum_suite.prometheus_ucn_audit
example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    PrometheusNoiseAudit.PrometheusNoiseAuditSuite := s.quantum_physics_full_suite.prometheus_noise_audit
example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    PrometheusUCNAudit.PrometheusUCNAuditSuite := s.quantum_physics_full_suite.prometheus_ucn_audit
example (s : MasterSuite.QuantumPhysicsFullSuite) :
    0 < PrometheusNoiseAudit.iidAnyFalseAlarm (1 / 10000) 10000 := s.prometheus_noise_audit.counterexample
example (s : MasterSuite.QuantumPhysicsFullSuite) :
    PrometheusUCNAudit.hypotheticalGross - 1 < 0 := s.prometheus_ucn_audit.deficit 1 (by norm_num)
