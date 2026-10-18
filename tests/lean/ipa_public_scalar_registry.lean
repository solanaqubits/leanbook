/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPAPublicScalarBindingContract

example : CryptoBulletproofsIPAPublicScalarBindingContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.ipa_public_scalar
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPAPublicScalarBindingContractSuite := r.crypto_suite.ipa_public_scalar
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPAPublicScalarBindingContractSuite :=
  r.crypto_full_suite.ipa_public_scalar
example : CryptoBulletproofsIPAPublicScalarBindingContractSuite := verification_suite
