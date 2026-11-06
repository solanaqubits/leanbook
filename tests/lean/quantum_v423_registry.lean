import Verification.MasterSuite

example : QuantumTensorStageEnvironment.QuantumTensorStageEnvironmentSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.tensor_environment

example : QuantumPostBSMEnvironment.QuantumPostBSMEnvironmentSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.post_bsm_environment
