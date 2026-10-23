import Verification.MasterSuite

open PrometheusFiniteBlockAudit
open scoped BigOperators

example : PrometheusFiniteBlockAuditSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.prometheus_finiteblock
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusFiniteBlockAuditSuite :=
  s.quantum_physics_full_suite.prometheus_finiteblock
example (s : MasterSuite.QuantumPhysicsFullSuite) (message : Fin 200 → Bool) :
    packetFailureProbability 100 message < 1 / 1000000000 :=
  s.prometheus_finiteblock.certified 200 (by norm_num) message
example (s : MasterSuite.QuantumPhysicsFullSuite) (k r : ℕ) :
    (∑ noise : Fin k → Fin r → Noise, productMass (productMass noiseMass) noise) = 1 :=
  s.prometheus_finiteblock.normalized k r
example (s : MasterSuite.QuantumPhysicsFullSuite) (message : Fin 12 → Bool) :
    packetFailureProbability 17 message ≤ 12 * (3 / 4 : ℚ) ^ 17 :=
  s.prometheus_finiteblock.finite_bound 12 17 message
