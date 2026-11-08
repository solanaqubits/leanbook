import Verification.MasterSuite

example : ClaimTransportContract.ClaimTransportSuite :=
  MasterSuite.distributed_systems_full_master_suite.{0, 0, 0}.claim_transport
