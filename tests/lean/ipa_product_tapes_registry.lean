/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPAProductTapeCandidateGeneratorContract

example : CryptoBulletproofsIPAProductTapeCandidateGeneratorContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0,
                                              0}).crypto_suite.ipa_product_tapes
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPAProductTapeCandidateGeneratorContractSuite
      := r.crypto_suite.ipa_product_tapes
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPAProductTapeCandidateGeneratorContractSuite
      := r.crypto_full_suite.ipa_product_tapes
example : CryptoBulletproofsIPAProductTapeCandidateGeneratorContractSuite := verification_suite
