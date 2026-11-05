import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumTwoQubitCPTP.QuantumTwoQubitCPTPSuite := r.two_qubit_cptp

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumBellCircuitRefinement.QuantumBellCircuitRefinementSuite := r.bell_circuit_refinement

example : QuantumTwoQubitCPTP.QuantumTwoQubitCPTPSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.two_qubit_cptp
