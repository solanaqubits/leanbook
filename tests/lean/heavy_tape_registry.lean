/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarHeavyTapeContract

example : CryptoHiddenScalarHeavyTapeContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.heavy_tape
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarHeavyTapeContractSuite := r.crypto_suite.heavy_tape
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarHeavyTapeContractSuite :=
  r.crypto_full_suite.heavy_tape
example : CryptoHiddenScalarHeavyTapeContractSuite := verification_suite
