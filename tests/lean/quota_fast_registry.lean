/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaFastContract

example : CryptoHiddenScalarQuotaFastContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_fast
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaFastContractSuite := r.crypto_suite.quota_fast
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaFastContractSuite :=
  r.crypto_full_suite.quota_fast
example : CryptoHiddenScalarQuotaFastContractSuite := verification_suite
