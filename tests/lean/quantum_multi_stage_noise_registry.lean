import Verification.MasterSuite

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumOrderedNoiseComposition.QuantumOrderedNoiseCompositionSuite :=
  r.ordered_noise_composition

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumMultiStageBSM.QuantumMultiStageBSMSuite := r.multi_stage_bsm

example : QuantumMultiStageBSM.QuantumMultiStageBSMSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.multi_stage_bsm
