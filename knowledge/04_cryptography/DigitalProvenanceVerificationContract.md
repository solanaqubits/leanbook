---
id: DigitalProvenanceVerificationContract
language: en
section: cryptography
source: Verification/DigitalProvenanceVerificationContract.lean
source_sha256: dd444795d6cb8305bf73dbcbc6bac6c93d3600132726c7e806508c35d6e9149f
novelty: not-assessed
status: reviewed
---

# Pure provenance verification contract — epsilon252

[Lean](../../Verification/DigitalProvenanceVerificationContract.lean).
Hierarchy: cryptography / bulletproofs-ipa / epsilon252.

CryptoBackend supplies sha256 and verifyEd25519 callbacks. Their implementations
and cryptographic security are separate obligations. ExpectedContext is supplied
independently: signer/key/role/session, challenge, policy version, n/j/epsilon and
expected context ID. VerificationPolicy supplies key lookup, revocation and a
predicate on the optional time claim. These inputs do not certify trust or clocks.

verifyProvenance strictly decodes the epsilon248 frame, compares every context
field, resolves the key, checks 32-byte keys and 64-byte signatures, revocation,
time policy, exact artifact sizes and callback digests, then the signature callback
on signingMessageV1 m. The existing domain prefix is added exactly once; no extra
application prehash is introduced. Failures return none; success carries the
manifest and authorization blocked. No network, IO or signing is performed.

checkManifest_iff relates execution to ManifestAccepted. verifyProvenance_iff
characterizes acceptance by FitsManifestLimits, exact canonical frame equality
and ManifestAccepted. verify_encoded_iff provides completeness for bounded
encodings. accepted_artifact_bindings and accepted_signature expose artifact and
exact-message obligations. Unknown keys, revoked keys and changed challenges
are proved rejected. The registry suite exports acceptance, blocked authorization,
artifact bindings and the signature message theorem.

38 runtime cases cover acceptance, all ten context fields, key/signature lengths,
missing and revoked keys, time policy and time components, artifact lengths and
digests, swapped files, malformed frames/EOF/limits and exact signing messages.
Synthetic callbacks are not crypto vectors. A colliding-hash counterexample
illustrates that digest equality does not establish byte equality. Repeated calls
accept again: a pure check does not consume a challenge or supply replay defense.
Formal examples and registry projections check theorem availability. Completed
verification evidence and integration identifiers are recorded separately.

No concrete crypto, key-distribution/CRL trust, real-clock qualification, atomic
replay registry, mathematical quota restoration, general resource bound or
permission elevation is established. Callers may supply an incorrect expected
context. Existing codec/reader layers are preserved. Novelty is not assessed.

Independent public validation for this source is recorded in [release v0.7.46](../../docs/release-v0.7.46.en.md).
