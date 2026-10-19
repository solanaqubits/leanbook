/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarSinglePathContract

example : CryptoHiddenScalarSinglePathContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.single_path
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarSinglePathContractSuite := r.crypto_suite.single_path
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarSinglePathContractSuite :=
  r.crypto_full_suite.single_path
example : CryptoHiddenScalarSinglePathContractSuite := verification_suite
