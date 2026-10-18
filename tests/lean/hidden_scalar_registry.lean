/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarInnerProductProtocolContract

example : CryptoHiddenScalarInnerProductProtocolContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.hidden_scalar_protocol
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarInnerProductProtocolContractSuite := r.crypto_suite.hidden_scalar_protocol
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarInnerProductProtocolContractSuite :=
  r.crypto_full_suite.hidden_scalar_protocol
example : CryptoHiddenScalarInnerProductProtocolContractSuite := verification_suite
