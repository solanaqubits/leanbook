import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumBellDiagonalInputs.QuantumBellDiagonalInputsSuite := r.bell_diagonal_inputs

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumBellDiagonalSwapping.QuantumBellDiagonalSwappingSuite := r.bell_diagonal_swapping

example : QuantumBellDiagonalSwapping.QuantumBellDiagonalSwappingSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.bell_diagonal_swapping
