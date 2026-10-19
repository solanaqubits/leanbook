/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarForkRecursiveQuotaContract

example : CryptoHiddenScalarForkRecursiveQuotaContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.fork_recursive_quota
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarForkRecursiveQuotaContractSuite := r.crypto_suite.fork_recursive_quota
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarForkRecursiveQuotaContractSuite :=
  r.crypto_full_suite.fork_recursive_quota
example : CryptoHiddenScalarForkRecursiveQuotaContractSuite := verification_suite
