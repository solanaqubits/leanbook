---
id: CryptoHiddenScalarQuotaProfileCodecContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaProfileCodecContract.lean
source_sha256: 0f2909a12c2c7d0a6ed841e9baf2a806e35523a2976a0f6d31a084735fa4a5a9
novelty: not-assessed
status: reviewed
---

# Canonical quota profile bytes QCP/01

[Lean](../../Verification/CryptoHiddenScalarQuotaProfileCodecContract.lean).
Epsilon243, cryptography/bulletproofs-ipa.

Frame: `51 43 50 01 | ULEB128(count) | Rational[count]`. The empty frame is
`51 43 50 01 00`. This domain differs from QCS/01 snapshots. No bound, cursor row,
j or epsilon is carried; the declared count does not become a trusted n.
Rationals reuse epsilon240's sign byte, minimal unsigned LEB128 magnitude and
positive denominator, coprimality and unique positive zero. Values outside [0,1]
are permitted algebraically; a probability interpretation needs separate premises.

`ProfileLimits` supplies maxSizeBytes and maxCoefficients. `Fits` bounds list length
and full encoded size, including large numerators and denominators. A zero byte cap
rejects every frame; a zero coefficient cap allows the empty five-byte frame.
`strictDecode` checks size before parsing, header/version, count before constructing
coefficients, individual rationals and exact EOF. It then checks Fits and exact
re-encoding equality. This explicit canonicality guard is not authentication.

`parseFrame_encode` uses existing suffix-aware primitive parser proofs.
`decode_encodeV1` proves Fits implies decoding the encoding returns the list.
`decode_canonical` proves successful decoding implies Fits and equality with the
original bytes. `decode_iff`, `encodeV1_injective` and `zero_size_refuses` follow.
The standalone byte layer has no expected quota parameters.

`decodeExpected?` separately checks the list against independent n/expected using
Matches from epsilon242. `decodeExpected_iff` characterizes its exact acceptance.
`restoreProfileBytes?` calls the existing typed restoration and returns its snapshot
projection. `restoreProfileBytes_iff` characterizes success by Fits of the expected
export, exact encoded bytes, ValidSnapshot under external n/p/j/epsilon and out=s.
The complete prefix and row check is preserved; valid bytes alone do not suffice.

There are 79 executable checks using independently calculated Python integer/Fraction
byte vectors, malformed/truncated/noncanonical frames, size/count boundaries, large
rationals, count=128, wrong context, domain confusion and restoration outcomes.
Six kernel examples apply theorems; four registry projections exercise integration.
Checks are finite and the audit is scoped, not a new full beta.

This codec module has no combined profile/snapshot bundle format. The separate
[QCP/01 reader](../../docs/quota-profile-reader.en.md) is included in this release. The input
ByteArray already exists; limits do not prove total RAM/CPU/time bounds for allocation,
list conversion, re-encoding or rational arithmetic. Neither bytes nor Matches establish
provenance of expected or detect coordinated replacement of all external context.
Prior snapshots, codecs, profile transfer and reader remain unchanged. Authorization
stays blocked; the Third Obligation stays OPEN. Novelty is not assessed.
