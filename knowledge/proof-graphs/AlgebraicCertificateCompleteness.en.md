---
id: AlgebraicCertificateCompleteness
language: en
section: proof-graphs
source: Verification/AlgebraicCertificateCompleteness.lean
source_sha256: 06000a837c112a793a8f0c9dd13f8c0e4a78de5637bd65ab5611fa70dc17c341
novelty: not-assessed
---

# Normalization completeness and rejection soundness

[Section](README.md) · [Lean source](../../Verification/AlgebraicCertificateCompleteness.lean)

Proves that zero polynomial denotation is equivalent to zero normalized representation. A false checkCert result entails nonzero residual denotation. This rejects the supplied multipliers, not the underlying mathematical implication, and does not construct a counterexample point.

## Interfaces and proof scope

- `exponentIndex_injective`
- `termDenote_eq_monomial`
- `coeff_denote`
- `denote_zero_iff_normalize_nil`
- `checkCert_true_iff_residual_zero`
- `checkCert_true_iff_identity`
- `checkCert_false_sound`
- `checkCert_false_iff_residual_ne_zero`
- `AlgebraicCertificateCompletenessSuite`
- `verification_suite`

The source types specify the actual hypotheses. See the [ALCC guide](../../docs/alcc.en.md) for execution and trust boundaries. Scientific priority is not assessed.
