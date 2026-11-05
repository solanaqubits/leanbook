import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumNoisyBellInstrument.QuantumNoisyBellInstrumentSuite := r.noisy_bell_instrument

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumNoisySwapping.QuantumNoisySwappingSuite := r.noisy_swapping

example : QuantumNoisySwapping.QuantumNoisySwappingSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.noisy_swapping
