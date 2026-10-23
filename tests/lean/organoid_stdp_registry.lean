import Verification.MasterSuite

open BiohybridOrganoidSynapseContract

example : BiohybridOrganoidSynapseSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.organoid_stdp

example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    BiohybridOrganoidSynapseSuite := s.quantum_physics_full_suite.organoid_stdp

example (r : MasterSuite.QuantumPhysicsFullSuite) (p : STDPParameters)
    (s : OrganoidSynapseState) (dt : ℤ) :
    0 ≤ (stdpUpdate p s dt).weight ∧ (stdpUpdate p s dt).weight ≤ s.wMax ∧
      (stdpUpdate p s dt).wMax = s.wMax := r.organoid_stdp.local_bounds p s dt

example (r : MasterSuite.QuantumPhysicsFullSuite) (K : ℕ) (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) :
    totalWeight (homeostaticNormalize B hB s) = min (totalWeight s) B :=
  r.organoid_stdp.norm_total K B hB s

example (r : MasterSuite.QuantumPhysicsFullSuite) (K : ℕ) (p : STDPParameters)
    (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K) (events : Fin K → Option ℤ) :
    totalWeight (ensembleStep p B hB s events) ≤ B :=
  r.organoid_stdp.composite_budget K p B hB s events

example (r : MasterSuite.QuantumPhysicsFullSuite) (p : STDPParameters)
    (s : OrganoidSynapseState) : eventUpdate p s none = s :=
  r.organoid_stdp.local_silence p s

example (r : MasterSuite.QuantumPhysicsFullSuite) (K : ℕ) (p : STDPParameters)
    (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K) (events : Fin K → Option ℤ)
    (he : ∀ i, events i = none) (hs : totalWeight s ≤ B) :
    ensembleStep p B hB s events = s := r.organoid_stdp.composite_silence K p B hB s events he hs
