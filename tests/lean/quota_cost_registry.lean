/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaCostContract

example : CryptoHiddenScalarQuotaCostContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_cost
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaCostContractSuite := r.crypto_suite.quota_cost
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaCostContractSuite :=
  r.crypto_full_suite.quota_cost
example : CryptoHiddenScalarQuotaCostContractSuite := verification_suite
