/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPAPartialBranchCacheResourceContract

example : CryptoBulletproofsIPAPartialBranchCacheResourceContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.ipa_partial_cache
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPAPartialBranchCacheResourceContractSuite := r.crypto_suite.ipa_partial_cache
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPAPartialBranchCacheResourceContractSuite :=
  r.crypto_full_suite.ipa_partial_cache
example : CryptoBulletproofsIPAPartialBranchCacheResourceContractSuite := verification_suite
