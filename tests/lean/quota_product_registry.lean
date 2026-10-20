/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaProductContract

example : CryptoHiddenScalarQuotaProductContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_product
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaProductContractSuite := r.crypto_suite.quota_product
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaProductContractSuite :=
  r.crypto_full_suite.quota_product
example : CryptoHiddenScalarQuotaProductContractSuite := verification_suite
