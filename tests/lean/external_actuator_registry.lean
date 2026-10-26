import Verification.MasterSuite

private abbrev migrationRegistry :=
  MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}

open ExternalActuatorContract
example : ExternalActuatorContractSuite :=
  migrationRegistry.distributed_suite.external_actuator
example (A : Type) [DecidableEq A] (auth conf : A → Prop)
    (events : List (Event A)) (s : State A) (h : Run auth conf initial events s) (id : A) :
    dispatchCount events id ≤ 1 :=
  migrationRegistry.distributed_suite.external_actuator.trace_bound
    A auth conf events s h id
