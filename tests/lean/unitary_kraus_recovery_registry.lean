import Verification.MasterSuite

open QuantumUnitaryKrausDiagonalizationRecoveryContract

example :
  QuantumUnitaryKrausDiagonalizationRecoveryContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0,
                                              0}).quantum_suite.unitary_kraus_recovery

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0,
                                              0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumUnitaryKrausDiagonalizationRecoveryContractSuite :=
  r.quantum_suite.unitary_kraus_recovery

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumUnitaryKrausDiagonalizationRecoveryContractSuite :=
  r.quantum_physics_full_suite.unitary_kraus_recovery
