/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarForkLocalDensityContract

example : CryptoHiddenScalarForkLocalDensityContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.fork_local_density
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarForkLocalDensityContractSuite := r.crypto_suite.fork_local_density
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarForkLocalDensityContractSuite :=
  r.crypto_full_suite.fork_local_density
example : CryptoHiddenScalarForkLocalDensityContractSuite := verification_suite
