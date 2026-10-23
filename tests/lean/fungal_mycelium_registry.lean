import Verification.MasterSuite

open FungalMyceliumMemristorContract

-- Registry projections, not independent physical validation.
example : FungalMyceliumMemristorSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.fungal_mycelium

example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    FungalMyceliumMemristorSuite := s.quantum_physics_full_suite.fungal_mycelium

example (s : MasterSuite.QuantumPhysicsFullSuite) :
    FungalMyceliumMemristorSuite := s.fungal_mycelium

example (r : MasterSuite.QuantumPhysicsFullSuite) (p : MemristorParameters)
    (s : MemristorState p) (V : ℚ) :
    p.Gmin ≤ (memristorStep s V).conductance ∧
      (memristorStep s V).conductance ≤ p.Gmax := r.fungal_mycelium.bounds p s V

example (r : MasterSuite.QuantumPhysicsFullSuite) (p : MemristorParameters)
    (s : MemristorState p) (V : ℚ) (h : |V| < p.Vth) :
    memristorStep s V = s := r.fungal_mycelium.retention p s V h

example (r : MasterSuite.QuantumPhysicsFullSuite) (p : MemristorParameters)
    (s : MemristorState p) :
    (downStep (upStep s)).conductance < (upStep (downStep s)).conductance :=
  r.fungal_mycelium.history p s

example (r : MasterSuite.QuantumPhysicsFullSuite) (Sth S : ℚ) :
    spikeGenerator Sth S = true ↔ Sth < S := r.fungal_mycelium.spike_characterization Sth S

example (r : MasterSuite.QuantumPhysicsFullSuite) (A γ : ℚ)
    (hA : 0 < A) (hγ : 0 < γ) (hγ1 : γ < 1) (x y : ℕ) (hxy : x < y) :
    spatialAmplitude A γ y < spatialAmplitude A γ x :=
  r.fungal_mycelium.spatial_decay A γ hA hγ hγ1 hxy
