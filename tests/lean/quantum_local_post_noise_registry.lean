import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumLocalPostNoise.QuantumLocalPostNoiseSuite := r.local_post_noise

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumLocalNoisySwapping.QuantumLocalNoisySwappingSuite := r.local_noisy_swapping

example : QuantumLocalNoisySwapping.QuantumLocalNoisySwappingSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.local_noisy_swapping
