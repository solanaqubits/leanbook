import Verification.MasterSuite
open ActuatorArbitrationContract
example : ActuatorArbitrationContractSuite :=
  MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}.distributed_suite.actuator_arbitration
example (policy : Request → Bool) (s : State) (r : Request) :
    (applyRequest policy s r).1.actuator = s.actuator :=
  MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}.distributed_suite.actuator_arbitration.history
    policy s r
