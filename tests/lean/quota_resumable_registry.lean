/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaResumableContract

example : CryptoHiddenScalarQuotaResumableContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_resumable
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaResumableContractSuite := r.crypto_suite.quota_resumable
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaResumableContractSuite :=
  r.crypto_full_suite.quota_resumable
example : CryptoHiddenScalarQuotaResumableContractSuite := verification_suite
