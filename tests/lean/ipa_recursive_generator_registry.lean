/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPARecursiveTreeGeneratorContract

example : CryptoBulletproofsIPARecursiveTreeGeneratorContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).crypto_suite.ipa_recursive_generator
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPARecursiveTreeGeneratorContractSuite := r.crypto_suite.ipa_recursive_generator
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPARecursiveTreeGeneratorContractSuite := r.crypto_full_suite.ipa_recursive_generator
example : CryptoBulletproofsIPARecursiveTreeGeneratorContractSuite := verification_suite
