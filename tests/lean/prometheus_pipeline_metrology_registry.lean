import Verification.MasterSuite

open PrometheusPipelinedQueue PrometheusMetrologyJitter

example : PrometheusPipelinedQueueSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.prometheus_pipeline
example : PrometheusMetrologyJitterSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.prometheus_metrology
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusPipelinedQueueSuite :=
  s.quantum_physics_full_suite.prometheus_pipeline
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusMetrologyJitterSuite :=
  s.quantum_physics_full_suite.prometheus_metrology
example (s : MasterSuite.QuantumPhysicsFullSuite) (period x y : ℝ)
    (hp : 0 < period) (he : PhaseEquivalent period x y) (hb : |x - y| < period) : x = y :=
  s.prometheus_metrology.unwrap period x y hp he hb
example (s : MasterSuite.QuantumPhysicsFullSuite) (q : PrometheusDecoderQueue.QueueInput)
    (e A J S : ℝ) (h : LaneEnvelope q e A J S) (i : ℕ) :
    PrometheusDecoderQueue.waiting q i ≤ J := s.prometheus_pipeline.wait_bound q e A J S h i
