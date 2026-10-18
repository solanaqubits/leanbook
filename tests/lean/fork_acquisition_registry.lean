/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoHiddenScalarForkAcquisitionContract

example : CryptoHiddenScalarForkAcquisitionContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.fork_acquisition
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarForkAcquisitionContractSuite := r.crypto_suite.fork_acquisition
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarForkAcquisitionContractSuite :=
  r.crypto_full_suite.fork_acquisition
example : CryptoHiddenScalarForkAcquisitionContractSuite := verification_suite
