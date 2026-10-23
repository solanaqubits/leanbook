import Verification.MasterSuite
open PrometheusNQKDAudit PrometheusTAKLAudit
example : PrometheusNQKDAuditSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.prometheus_nqkd
example : PrometheusTAKLAuditSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.prometheus_takl
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusNQKDAuditSuite :=
  s.quantum_physics_full_suite.prometheus_nqkd
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusTAKLAuditSuite :=
  s.quantum_physics_full_suite.prometheus_takl
example (s : MasterSuite.QuantumPhysicsFullSuite) (rho : QuantumBB84ProtocolQBER.QMatrix) :
    coinChannel rho = rho := s.prometheus_nqkd.counterexample rho
example (s : MasterSuite.QuantumPhysicsFullSuite) (h d phi : ℝ) (M : ℂ) :
    goldenRate h (unitPhase phi * M) d = goldenRate h M d :=
  s.prometheus_takl.phase_invariance h d phi M
