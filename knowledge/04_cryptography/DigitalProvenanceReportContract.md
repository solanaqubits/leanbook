---
id: DigitalProvenanceReportContract
language: en
section: cryptography
source: Verification/DigitalProvenanceReportContract.lean
source_sha256: cfc5b6d28b02f8fe9fec07d2f1076a926ad926621899fae160c28821c5897b41
novelty: not-assessed
status: reviewed
---

# Granular provenance verification — epsilon258

[Lean](../../Verification/DigitalProvenanceReportContract.lean).
cryptography / bulletproofs-ipa.

The new namespace preserves epsilon252 and sequential replay epsilon255 APIs.
Fallible CryptoBackend callbacks distinguish errors from mismatches. The independent
ExpectedContext supplies a finite key registry, signer/role/session/policy/context,
n/j/epsilon, signer/key-scoped revocation, optional challenge and time window.
Distinct key IDs permit rotation; duplicate signer/key pairs and malformed public
key lengths reject the registry globally. Key refusal precedence is duplicate,
key length, signer, manifest role/policy, unique candidate, candidate role/policy,
then revocation. No package-provided key is trusted.

InputsFit bounds artifact sizes, registry/revocation counts, every external field
representation and the canonical manifest. prepareVerification has no backend
argument: it returns a limit error or an explicit data-only request plan. The
interpreter processes the signature and then two artifact hash requests. Signature
requests require an authorized 32-byte key and a 64-byte signature and use exactly
signingMessageV1. Artifact size mismatches suppress the corresponding hash request.
Independent checks continue after signature refusal.

verify_result_iff characterizes report production, not overall acceptance.
limit_refusal proves error plus an empty request plan; limit_backend_independent
separately proves extensional independence. These are model properties, not a
machine trace, compiler/FFI theorem or memory bound. selected_key_sound proves
external membership, expected signer/key/role/policy, non-revocation and key size.
planned_signature_sound and executed_signature_sound establish exact message
forwarding and callback success. Artifact matched iff the size and callback digest
match is proved for both artifacts. Context, challenge and time have separate iff
statements. Authorization has only the blocked constructor.

Invalid time windows take precedence over missing claims. Scale/unit mismatches
remain distinct from expired/future claims. Within-window checks describe a signed
claim relative to supplied policy, not physical delivery freshness. Challenge
matching does not consume a challenge. Hash agreement is not a proof of byte equality,
physical provenance, mathematical cursor validity or external-context trust.

69 synthetic runtime cases exercise refusal, boundaries, rotation and request order;
the callbacks are not SHA-256/Ed25519 implementations. Formal examples and existing
layer regressions are recorded separately with actual evidence. This API accepts
a typed manifest; raw-byte parsing stays in epsilon248. Novelty is not assessed.
Concrete crypto, atomic replay, physical qualification and general resource bounds
are separate obligations. No permission elevation or public release is supplied.

Independent public validation is recorded in [release v0.7.47](../../docs/release-v0.7.47.en.md). Historical development checks above do not replace public checks.
