---
id: DigitalProvenanceManifestContract
language: en
section: cryptography
source: Verification/DigitalProvenanceManifestContract.lean
source_sha256: 153214c8b8e18ca6c5e8d51eb8929e9956d65b52c6183de8f75901a8a619fab5
novelty: not-assessed
status: reviewed
---

# Canonical Provenance v1 manifest — epsilon248

[Lean](../../Verification/DigitalProvenanceManifestContract.lean).
Originally developed with scoped verification.

QPM/01 starts with `51 50 4d 01`, followed in order by signerId, keyId, roleId,
sessionId, challenge, policyVersion, snapshot, profile, n, j, epsilon,
expectedContextId, claimedTime. Strings use minimal ULEB128 UTF-8 byte lengths
and exact valid UTF-8, without normalization or replacement. Challenge uses a
length-prefixed raw blob. Each artifact binding is ULEB128(sizeBytes), ULEB128(32),
and 32 opaque digest bytes. No SHA-256 computation is implemented.
Nat uses minimal ULEB128. Epsilon reuses epsilon240 canonical rational encoding.
Optional time uses tag 00/01, scale/unit strings and sign byte plus minimal ULEB128
magnitude for Int, rejecting negative zero. Signatures are outside the frame.

signingMessageV1 prepends exactly the ASCII bytes
`SIMLAB_PROVENANCE_V1_SHA256_ED25519:` to encodeManifestV1. There is no NUL or
application prehash. A future Ed25519 backend must receive this exact message.

FitsManifestLimits bounds every UTF-8 string, challenge and the entire encoding,
including unbounded integer/rational fields. requiredStringLimit is the maximum,
not the sum. Zero field caps allow empty fields; zero total cap rejects all frames.
The decoder checks total size before list conversion, field lengths before slicing,
UTF-8, digest length, exact EOF, then Fits and exact re-encoding equality.

Proved: decode_encodeManifestV1, decodeManifest_canonical,
encodeManifestV1_injective, signingMessageV1_injective. Suffix parser lemmas prove
completeness; the explicit canonical guard proves soundness. Common sufficient
limits give encoding injectivity, and fixed-prefix cancellation gives message
injectivity. All four are exported through the registry suite. Digest256 only
proves 32 bytes; AuthorizationStatus has only blocked, without a verifier report.

Tests use independent Python byte expectations, UTF-8, integer/rational and cap
boundaries, truncations, extra bytes, nonminimal ULEB128, wrong digest lengths and
noncanonical signs/tags/zero. Public validation is recorded with the release.
This is not a new full-library beta or an exhaustive test claim.

No cryptographic backend, verifyProvenance, key registry/CRL validation, time policy,
atomic challenge consumption, manifest file reader or signature envelope codec.
No cryptographic/security/provenance, mathematical snapshot validity, or total
memory/time theorem follows. Input bytes already reside in memory; parsing and
re-encoding allocate additional memory. Prior quota layers remain unchanged.
Authorization blocked; hardware paused; Third Obligation OPEN. Novelty not assessed.
