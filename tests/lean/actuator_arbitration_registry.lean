import Verification.MasterSuite

private abbrev migrationRegistry :=
  MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}

open ActuatorArbitrationContract
example : ActuatorArbitrationContractSuite :=
  migrationRegistry.distributed_suite.actuator_arbitration
example (policy : Request → Bool) (s : State) (r : Request) :
    (applyRequest policy s r).1.actuator = s.actuator :=
  migrationRegistry.distributed_suite.actuator_arbitration.history
    policy s r
