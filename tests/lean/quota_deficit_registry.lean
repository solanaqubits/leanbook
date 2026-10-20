/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaDeficitContract

example : CryptoHiddenScalarQuotaDeficitContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_deficit
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaDeficitContractSuite := r.crypto_suite.quota_deficit
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaDeficitContractSuite :=
  r.crypto_full_suite.quota_deficit
example : CryptoHiddenScalarQuotaDeficitContractSuite := verification_suite
