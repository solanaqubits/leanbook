/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaStreamingContract

example : CryptoHiddenScalarQuotaStreamingContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_streaming
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaStreamingContractSuite := r.crypto_suite.quota_streaming
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaStreamingContractSuite :=
  r.crypto_full_suite.quota_streaming
example : CryptoHiddenScalarQuotaStreamingContractSuite := verification_suite
