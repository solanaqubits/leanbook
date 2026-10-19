/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarForkScheduleProgressContract

example : CryptoHiddenScalarForkScheduleProgressContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.fork_schedule
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarForkScheduleProgressContractSuite := r.crypto_suite.fork_schedule
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarForkScheduleProgressContractSuite :=
  r.crypto_full_suite.fork_schedule
example : CryptoHiddenScalarForkScheduleProgressContractSuite := verification_suite
