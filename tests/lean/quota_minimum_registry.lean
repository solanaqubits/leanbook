/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaMinimumContract

example : CryptoHiddenScalarQuotaMinimumContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_minimum
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaMinimumContractSuite := r.crypto_suite.quota_minimum
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaMinimumContractSuite :=
  r.crypto_full_suite.quota_minimum
example : CryptoHiddenScalarQuotaMinimumContractSuite := verification_suite
