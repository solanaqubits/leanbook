/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarInnerProductCompressionContract

example : CryptoHiddenScalarInnerProductCompressionContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.hidden_scalar_compression
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarInnerProductCompressionContractSuite
      := r.crypto_suite.hidden_scalar_compression
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarInnerProductCompressionContractSuite :=
  r.crypto_full_suite.hidden_scalar_compression
example : CryptoHiddenScalarInnerProductCompressionContractSuite := verification_suite
