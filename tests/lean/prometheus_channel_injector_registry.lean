import Verification.MasterSuite

open PrometheusChannelAndInjectorAudit

example : PrometheusChannelAndInjectorAuditSuite :=
  (MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}).quantum_suite.prometheus_channel
example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    PrometheusChannelAndInjectorAuditSuite := s.quantum_physics_full_suite.prometheus_channel
example (s : MasterSuite.QuantumPhysicsFullSuite) : 3 / 10 < observedCapacity :=
  s.prometheus_channel.capacity
example (s : MasterSuite.QuantumPhysicsFullSuite) : observedCapacity < codeRate 1 1 :=
  s.prometheus_channel.finite_counterexample
example (s : MasterSuite.QuantumPhysicsFullSuite) : neutronKineticFraction < 1 :=
  s.prometheus_channel.fraction.2.2
