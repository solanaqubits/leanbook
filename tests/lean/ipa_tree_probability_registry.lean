/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPATreeProbabilityContract

example : CryptoBulletproofsIPATreeProbabilityContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0,
                                              0}).crypto_suite.ipa_tree_probability
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPATreeProbabilityContractSuite := r.crypto_suite.ipa_tree_probability
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPATreeProbabilityContractSuite := r.crypto_full_suite.ipa_tree_probability
example : CryptoBulletproofsIPATreeProbabilityContractSuite := verification_suite
