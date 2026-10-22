import Verification.MasterSuite

open PrometheusPiModelContract

example : PrometheusPiModelContractSuite :=
  (MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}).quantum_suite.prometheus_pi

example (s : MasterSuite.QuantumPhysicsFullSuite) : PrometheusPiModelContractSuite :=
  s.prometheus_pi

example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PrometheusPiModelContractSuite :=
  s.quantum_physics_full_suite.prometheus_pi

example (s : MasterSuite.QuantumPhysicsFullSuite) :
    350 * chargeFactor 6 6 < chargeFactor 110 74 := s.prometheus_pi.charge_advantage

example (s : MasterSuite.QuantumPhysicsFullSuite) (c : ℝ) (hc : 0 < c) :
    particleTime c < fiberTime c := s.prometheus_pi.latency c hc
