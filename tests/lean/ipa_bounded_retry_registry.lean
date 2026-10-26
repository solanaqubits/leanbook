/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPABoundedRetryContract

example : CryptoBulletproofsIPABoundedRetryContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0,
                                              0}).crypto_suite.ipa_bounded_retry
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPABoundedRetryContractSuite := r.crypto_suite.ipa_bounded_retry
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPABoundedRetryContractSuite := r.crypto_full_suite.ipa_bounded_retry
example : CryptoBulletproofsIPABoundedRetryContractSuite := verification_suite
