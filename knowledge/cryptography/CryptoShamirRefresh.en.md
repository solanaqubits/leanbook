---
id: CryptoShamirRefresh
language: en
section: cryptography
source: Verification/CryptoShamirRefresh.lean
source_sha256: 92013c8ee1287524ac6b48b6803512e44fae6386666c812633e01a280038c812
novelty: not-assessed
status: reviewed
---

# Uniform zero-constant polynomial refresh

Adding a degree-bounded zero-constant polynomial preserves the secret and adds its evaluation to each share. For each fixed old sharing, addition gives a bijection from zero-secret masks to the entire same-secret polynomial fiber. A uniform mask therefore yields the uniform law on that fiber, independent of the previous sharing. Sequential refreshes compose, and Feldman coefficient commitments update additively.

The finite-field result concerns the full polynomial distribution for a fixed previous sharing. It does not assert independence after arbitrary correlated observations of old shares, masks and new shares. Erasure, a mobile adversary, private transport and a refresh protocol are not modeled. Tests include changed shares, unchanged secret, inverse recovery, exact probability-law applications and a nonzero-constant mask excluded by the type.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [refresh_share](../../Verification/CryptoShamirRefresh.lean#L20)
- [refresh_secret](../../Verification/CryptoShamirRefresh.lean#L23)
- [refresh_uniform](../../Verification/CryptoShamirRefresh.lean#L38)
- [old_sharing_independent](../../Verification/CryptoShamirRefresh.lean#L42)
- [sequential_refresh](../../Verification/CryptoShamirRefresh.lean#L45)
- [commitment_update](../../Verification/CryptoShamirRefresh.lean#L50)
- [zero_mask_unchanged](../../Verification/CryptoShamirRefresh.lean#L57)
- [verification_suite](../../Verification/CryptoShamirRefresh.lean#L68)
