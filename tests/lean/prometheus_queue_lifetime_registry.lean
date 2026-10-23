import Verification.MasterSuite

open PrometheusVariableQueue PrometheusLifetimeInformation

example : PrometheusVariableQueueSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.prometheus_variable_queue
example : PrometheusLifetimeInformationSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.prometheus_lifetime_information
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusVariableQueueSuite :=
  s.quantum_physics_full_suite.prometheus_variable_queue
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusLifetimeInformationSuite :=
  s.quantum_physics_full_suite.prometheus_lifetime_information
example (s : MasterSuite.QuantumPhysicsFullSuite) (capacity : ℕ) (a v : ℕ → ℕ) (n : ℕ) :
    Balanced (run capacity a v n) := s.prometheus_variable_queue.conservation capacity a v n
example (s : MasterSuite.QuantumPhysicsFullSuite) :
    effectiveRate 1 0 = effectiveRate 2 (1 / 2) ∧ (1 : ℝ) ≠ 2 :=
  s.prometheus_lifetime_information.nonidentifiable
