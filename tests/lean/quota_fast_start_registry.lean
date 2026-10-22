/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaFastStartContract

example : CryptoHiddenScalarQuotaFastStartContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_fast_start
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaFastStartContractSuite := r.crypto_suite.quota_fast_start
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaFastStartContractSuite :=
  r.crypto_full_suite.quota_fast_start
example : CryptoHiddenScalarQuotaFastStartContractSuite := verification_suite
