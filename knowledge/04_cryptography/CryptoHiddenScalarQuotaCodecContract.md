---
id: CryptoHiddenScalarQuotaCodecContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaCodecContract.lean
novelty: not-assessed
status: reviewed
---

# Canonical bounded byte codec for quota cursor snapshots

Epsilon240, cryptography/bulletproofs-ipa.
[Lean](../../Verification/CryptoHiddenScalarQuotaCodecContract.lean) ·
[Normative v1 format](../../docs/quota-codec-v1.en.md).

QCS/01 frames contain minimal ULEB128 bound/count and canonical signed rationals.
Fits bounds bound, row length and the full encoded byte size. strictDecode checks
input size before list conversion, bound/count before parsing rows, rational
canonicality, EOF, then exact re-encoding equality. No hash substitutes for equality.

The kernel-checked decode_encodeV1 and decode_canonical establish the specified
round trip and canonical acceptance. Prefix parser round trips support the forward
proof; the inverse uses the deliberate exact re-encoding guard. encodeV1_injective,
decode_iff, decode_unique and zero_size_refuses follow. The quota_codec suite is
available through the central and hundred registries. Allowed axioms remain only
propext, Classical.choice and Quot.sound; no sorry or custom axioms.

42 executable fixed-byte cases and 57 kernel examples (five registry applications)
cover valid frames, ULEB boundaries, large rationals, exact limits and malformed
encodings. Expected finite bytes use independent Python shifts/Fraction arithmetic.
These tests are not independent universal semantic verification.

The API receives an already-read ByteArray. It is not a bounded file/network
reader and does not prove memory/time complexity of list conversion, recursion,
arbitrary-precision arithmetic or re-encoding. It neither transfers p(i) nor
validates mathematical prefix invariants, provenance or authorization. Mathematical
restoration remains separate in epsilon239. This is scoped verification, not a new
full beta checkpoint.
