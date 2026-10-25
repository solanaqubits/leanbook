---
id: AlgebraicCertificateVerify
language: en
section: proof-graphs
source: Verification/AlgebraicCertificateVerify.lean
source_sha256: 77ce6f0f9e90094069edc61173d3d51145635be0d171ed5323c7289d7768df8c
novelty: not-assessed
---

# Canonical bytes to certificate verdict

[Section](README.md) · [Lean source](../../Verification/AlgebraicCertificateVerify.lean)

verifyCertificateBytes returns Option Bool. none is exactly a bound-decoder refusal; some true entails a bound task with zero residual; some false entails a bound task with nonzero residual. The latter refutes this certificate only. Input acceptance completeness, Python equivalence and OS/runtime correctness are not proved.

## Interfaces and proof scope

- `verifyCertificateBytes`
- `denote_residual_eq_delta`
- `verifyCertificateBytes_none_iff`
- `verifyCertificateBytes_some_iff`
- `verifyCertificateBytes_true_sound`
- `verifyCertificateBytes_false_sound`

The source types specify the actual hypotheses. See the [ALCC guide](../../docs/alcc.en.md) for execution and trust boundaries. Scientific priority is not assessed.
