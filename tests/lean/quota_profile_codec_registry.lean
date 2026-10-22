import Verification.MasterSuite
open CryptoHiddenScalarQuotaProfileCodecContract
open CryptoHiddenScalarQuotaResumableContract

example : CryptoHiddenScalarQuotaProfileCodecContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_profile_codec
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaProfileCodecContractSuite := r.crypto_suite.quota_profile_codec
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaProfileCodecContractSuite := r.crypto_full_suite.quota_profile_codec
example (r : MasterSuite.VerificationMasterRegistry) (l xs) (h : Fits l xs) :
    strictDecode l (encodeV1 xs) = some xs :=
  r.crypto_suite.quota_profile_codec.round_trip l xs h
