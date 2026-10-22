/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaFastChainContract

example : CryptoHiddenScalarQuotaFastChainContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_fast_chain
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaFastChainContractSuite := r.crypto_suite.quota_fast_chain
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaFastChainContractSuite :=
  r.crypto_full_suite.quota_fast_chain
example : CryptoHiddenScalarQuotaFastChainContractSuite := verification_suite
