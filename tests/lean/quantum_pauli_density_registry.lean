import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumPauliMatrix.QuantumPauliMatrixSuite := r.pauli_matrix

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumPauliDensityBridge.QuantumPauliDensityBridgeSuite := r.pauli_density_bridge

example : QuantumPauliDensityBridge.QuantumPauliDensityBridgeSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.pauli_density_bridge
