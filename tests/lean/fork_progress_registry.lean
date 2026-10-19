/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarForkProgressProbabilityContract

example : CryptoHiddenScalarForkProgressProbabilityContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.fork_progress
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarForkProgressProbabilityContractSuite := r.crypto_suite.fork_progress
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarForkProgressProbabilityContractSuite :=
  r.crypto_full_suite.fork_progress
example : CryptoHiddenScalarForkProgressProbabilityContractSuite := verification_suite
