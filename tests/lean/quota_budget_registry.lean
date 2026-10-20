/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaBudgetContract

example : CryptoHiddenScalarQuotaBudgetContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_budget
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaBudgetContractSuite := r.crypto_suite.quota_budget
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaBudgetContractSuite :=
  r.crypto_full_suite.quota_budget
example : CryptoHiddenScalarQuotaBudgetContractSuite := verification_suite
