import Verification.MasterSuite

open PrometheusDecoderQueue

example : PrometheusDecoderQueueSuite :=
  (MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}).quantum_suite.prometheus_queue
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusDecoderQueueSuite :=
  s.quantum_physics_full_suite.prometheus_queue
example (s : MasterSuite.QuantumPhysicsFullSuite) : frameSerializationMs = 96 / 1000 :=
  s.prometheus_queue.serialize_exact
example (s : MasterSuite.QuantumPhysicsFullSuite) :
    waiting (periodicQueue 0 frameSerializationMs 1) 1 = 904 / 1000 :=
  s.prometheus_queue.one_ms_backlog
example (s : MasterSuite.QuantumPhysicsFullSuite) (q : QueueInput) (i : ℕ) :
    0 ≤ waiting q i := s.prometheus_queue.nonnegative q i
example (s : MasterSuite.QuantumPhysicsFullSuite) (bound : ℝ) :
    ∃ i, bound < waiting (periodicQueue 0 1 2) i :=
  (s.prometheus_queue.physical_overload 0 1 2 (by norm_num) (by norm_num)).2 bound
