/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPAPedersenOpeningConsistencyContract

example : CryptoBulletproofsIPAPedersenOpeningConsistencyContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.ipa_pedersen_consistency
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPAPedersenOpeningConsistencyContractSuite
      := r.crypto_suite.ipa_pedersen_consistency
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPAPedersenOpeningConsistencyContractSuite :=
  r.crypto_full_suite.ipa_pedersen_consistency
example : CryptoBulletproofsIPAPedersenOpeningConsistencyContractSuite := verification_suite
