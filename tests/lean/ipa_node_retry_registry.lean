/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract

example : CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0,
                                              0}).crypto_suite.ipa_node_retry
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContractSuite := r.crypto_suite.ipa_node_retry
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContractSuite
      := r.crypto_full_suite.ipa_node_retry
example : CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContractSuite := verification_suite
