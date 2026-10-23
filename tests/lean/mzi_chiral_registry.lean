import Verification.MasterSuite

open PhotonicsMachZehnderChiralContract

example : PhotonicsMachZehnderChiralSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.mzi_chiral

example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PhotonicsMachZehnderChiralSuite :=
  s.quantum_physics_full_suite.mzi_chiral

example (s : MasterSuite.QuantumPhysicsFullSuite) (φ : ℝ) (v : Amp2) :
    intensity (mziStep φ v) = intensity v := s.mzi_chiral.mzi_intensity φ v

/-- Canonical-input power agreement does not assert equal amplitude conventions. -/
example (φ : ℝ) :
    Complex.normSq (mziStep φ (1, 0)).1 =
      PhotonicsBeamSplitterPhaseShift.probability (1 / 2) φ 0 ∧
    Complex.normSq (mziStep φ (1, 0)).2 =
      PhotonicsBeamSplitterPhaseShift.probability (1 / 2) φ 1 := by
  obtain ⟨h₀, h₁⟩ := mzi_routing_half_angles φ
  obtain ⟨g₀, g₁⟩ := PhotonicsBeamSplitterPhaseShift.mzi_balanced_probabilities φ
  exact ⟨h₀.trans g₀.symm, h₁.trans g₁.symm⟩
