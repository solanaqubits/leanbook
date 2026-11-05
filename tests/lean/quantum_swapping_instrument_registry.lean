import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumRectangularSwapping.QuantumRectangularSwappingSuite := r.rectangular_swapping

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumSwappingInstrument.QuantumSwappingInstrumentSuite := r.swapping_instrument

example : QuantumSwappingInstrument.QuantumSwappingInstrumentSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.swapping_instrument
