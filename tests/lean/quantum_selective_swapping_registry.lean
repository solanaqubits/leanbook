import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumGeneralBellReadout.QuantumGeneralBellReadoutSuite := r.general_bell_readout

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumSelectiveSwapping.QuantumSelectiveSwappingSuite := r.selective_swapping

example : QuantumSelectiveSwapping.QuantumSelectiveSwappingSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.selective_swapping
