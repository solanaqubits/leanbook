import Verification.MasterSuite

open SpintronicSkyrmionSynapseContract

example : SpintronicSkyrmionSynapseSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.skyrmion_synapse

example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    SpintronicSkyrmionSynapseSuite := s.quantum_physics_full_suite.skyrmion_synapse

example (suite : MasterSuite.QuantumPhysicsFullSuite) (N : ℕ) (hN : 0 < N)
    (s : SkyrmionSynapse N) : 0 ≤ weight s ∧ weight s ≤ 1 :=
  suite.skyrmion_synapse.weight_bounds N hN s

example (suite : MasterSuite.QuantumPhysicsFullSuite) (N k : ℕ) (hN : 0 < N)
    (s : SkyrmionSynapse N) (hk : N ≤ k) :
    (repeatPulse .Potentiate k s).count = N ∧ weight (repeatPulse .Potentiate k s) = 1 :=
  suite.skyrmion_synapse.potentiation_saturation N hN k s hk

example (suite : MasterSuite.QuantumPhysicsFullSuite) (N : ℕ) (t I : ℚ)
    (s : SkyrmionSynapse N) (hI : |I| < t) : stateUpdate t I s = s :=
  suite.skyrmion_synapse.inactive_identity N t I s hI
