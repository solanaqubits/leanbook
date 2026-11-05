import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumOutcomeInstrument.QuantumOutcomeInstrumentSuite := r.outcome_instrument

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumNullConditioning.QuantumNullConditioningSuite := r.null_conditioning

example : QuantumNullConditioning.QuantumNullConditioningSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.null_conditioning
