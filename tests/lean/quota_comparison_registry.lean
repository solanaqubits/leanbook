/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaComparisonContract

example : CryptoHiddenScalarQuotaComparisonContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_comparison
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaComparisonContractSuite := r.crypto_suite.quota_comparison
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaComparisonContractSuite :=
  r.crypto_full_suite.quota_comparison
example : CryptoHiddenScalarQuotaComparisonContractSuite := verification_suite
