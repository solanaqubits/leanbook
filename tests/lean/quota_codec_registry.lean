import Verification.MasterSuite
open CryptoHiddenScalarQuotaCodecContract
open CryptoHiddenScalarQuotaSnapshotContract

example : CryptoHiddenScalarQuotaCodecContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_codec
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaCodecContractSuite := r.crypto_suite.quota_codec
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaCodecContractSuite := r.crypto_full_suite.quota_codec
example (r : MasterSuite.VerificationMasterRegistry) (limits : FitsLimits)
    (s : QuotaCursorSnapshot) (h : Fits limits s) :
    strictDecode limits (encodeV1 s) = some s := r.crypto_suite.quota_codec.round_trip limits s h
example (r : MasterSuite.VerificationMasterRegistry) (limits : FitsLimits)
    (bytes : ByteArray) (s : QuotaCursorSnapshot) (h : strictDecode limits bytes = some s) :
    Fits limits s ∧ encodeV1 s = bytes := r.crypto_suite.quota_codec.canonical limits bytes s h
