import Verification.MasterSuite
example : MlDsaPackedPredicate.MlDsaPackedPredicateSuite :=
  MasterSuite.crypto_full_master_suite.{0, 0, 0, 0, 0, 0}.mldsa_packed
example : MlDsaWtBranch.MlDsaWtBranchSuite :=
  MasterSuite.crypto_full_master_suite.{0, 0, 0, 0, 0, 0}.mldsa_wt
