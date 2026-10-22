import Verification.MasterSuite
open CryptoHiddenScalarQuotaProfileContract
open CryptoHiddenScalarQuotaResumableContract

example : CryptoHiddenScalarQuotaProfileContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_profile
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaProfileContractSuite := r.crypto_suite.quota_profile
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaProfileContractSuite := r.crypto_full_suite.quota_profile
example (r : MasterSuite.VerificationMasterRegistry) (n p xs) :
    Matches n p xs ↔ xs = exportProfile n p :=
  r.crypto_suite.quota_profile.canonical n p xs
