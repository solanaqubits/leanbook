import Verification.MasterSuite

open OptospintronicTransducerContract

example : OptospintronicTransducerSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.optospintronic

example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    OptospintronicTransducerSuite := s.quantum_physics_full_suite.optospintronic

example (s : MasterSuite.QuantumPhysicsFullSuite) :
    OptospintronicTransducerSuite := s.optospintronic

example (r : MasterSuite.QuantumPhysicsFullSuite) (C : ℕ)
    (s : SpinReservoirState C) (p : OpticalPulse) :
    |(transferMomentum p s).spinZ - s.spinZ| ≤ couplingBudget p :=
  r.optospintronic.transfer_bound C s p

example (r : MasterSuite.QuantumPhysicsFullSuite) (C : ℕ)
    (s : SpinReservoirState C) (p : OpticalPulse) :
    s.spinZ + signedIncidentMomentum p =
      (transferMomentum p s).spinZ + opticalOutputMomentum s p :=
  r.optospintronic.conservation C s p

example (r : MasterSuite.QuantumPhysicsFullSuite) (C : ℕ)
    (s : SpinReservoirState C) (p : OpticalPulse) :
    -(C : ℚ) ≤ (transferMomentum p s).spinZ ∧
      (transferMomentum p s).spinZ ≤ (C : ℚ) := r.optospintronic.saturation C s p

example (r : MasterSuite.QuantumPhysicsFullSuite) (C : ℕ)
    (s : SpinReservoirState C) (p : OpticalPulse) :
    |opticalOutputMomentum s p| ≤ (p.photonCount : ℚ) :=
  r.optospintronic.output_bound C s p

example (r : MasterSuite.QuantumPhysicsFullSuite) (C : ℕ)
    (s : SpinReservoirState C) (p : OpticalPulse) (h : p.couplingEfficiency = 0) :
    transferMomentum p s = s := r.optospintronic.zero_efficiency C s p h
