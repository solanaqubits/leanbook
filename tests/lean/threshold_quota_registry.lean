/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarThresholdQuotaContract

example : CryptoHiddenScalarThresholdQuotaContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.threshold_quota
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarThresholdQuotaContractSuite := r.crypto_suite.threshold_quota
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarThresholdQuotaContractSuite :=
  r.crypto_full_suite.threshold_quota
example : CryptoHiddenScalarThresholdQuotaContractSuite := verification_suite
