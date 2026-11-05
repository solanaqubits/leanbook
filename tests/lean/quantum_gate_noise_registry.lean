import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumGateNoiseComposition.QuantumGateNoiseCompositionSuite := r.gate_noise_composition

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumCentralDepolarization.QuantumCentralDepolarizationSuite := r.central_depolarization

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumNoisyVisibility.QuantumNoisyVisibilitySuite := r.noisy_visibility

example : QuantumNoisyVisibility.QuantumNoisyVisibilitySuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.noisy_visibility
