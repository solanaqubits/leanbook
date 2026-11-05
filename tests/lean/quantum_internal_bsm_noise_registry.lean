import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumNoiseTransport.QuantumNoiseTransportSuite := r.noise_transport

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumInternalBSMNoise.QuantumInternalBSMNoiseSuite := r.internal_bsm_noise

example : QuantumInternalBSMNoise.QuantumInternalBSMNoiseSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.internal_bsm_noise
