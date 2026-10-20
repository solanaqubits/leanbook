/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarQuotaTabularContract

example : CryptoHiddenScalarQuotaTabularContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_tabular
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaTabularContractSuite := r.crypto_suite.quota_tabular
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaTabularContractSuite :=
  r.crypto_full_suite.quota_tabular
example : CryptoHiddenScalarQuotaTabularContractSuite := verification_suite
