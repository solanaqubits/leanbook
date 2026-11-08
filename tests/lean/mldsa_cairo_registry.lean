import Verification.MasterSuiteComponents

example : MlDsaCairoBlockSuite.CairoBlockSuite :=
  MasterSuite.crypto_full_master_suite.{0, 0, 0, 0, 0, 0}.mldsa_cairo
