/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarTapeAverageContract

example : CryptoHiddenScalarTapeAverageContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.tape_average
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarTapeAverageContractSuite := r.crypto_suite.tape_average
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarTapeAverageContractSuite :=
  r.crypto_full_suite.tape_average
example : CryptoHiddenScalarTapeAverageContractSuite := verification_suite
