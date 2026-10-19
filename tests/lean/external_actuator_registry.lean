import Verification.MasterSuite
open ExternalActuatorContract
example : ExternalActuatorContractSuite :=
  MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}.distributed_suite.external_actuator
example (A : Type) [DecidableEq A] (auth conf : A → Prop)
    (events : List (Event A)) (s : State A) (h : Run auth conf initial events s) (id : A) :
    dispatchCount events id ≤ 1 :=
  MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}.distributed_suite.external_actuator.trace_bound
    A auth conf events s h id
