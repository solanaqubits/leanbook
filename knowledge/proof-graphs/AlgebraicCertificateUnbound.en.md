---
id: AlgebraicCertificateUnbound
language: en
section: proof-graphs
source: Verification/AlgebraicCertificateUnbound.lean
source_sha256: cc5269996a3a9fbc1e70cb73f26f681d683b7bcade785e96eea4008fece63cc0
novelty: not-assessed
---

# Byte-to-task composition

[Section](README.md) · [Lean source](../../Verification/AlgebraicCertificateUnbound.lean)

Composes canonical parsing of two independent byte streams with typed schema decoding. The independent UnboundTaskRel relation supports end-to-end soundness and relational uniqueness. Its result has no cryptographic passport binding.

## Interfaces and proof scope

- `UnboundTaskRel`
- `decodeFromBytes`
- `decodeFromBytes_success_iff`
- `unboundTaskRel_deterministic`
- `decodeFromBytes_sound`
- `decodeFromBytes_unique`
- `unboundTaskRel_canonical_bytes`
- `decodeFromBytes_serialized`
- `accepted_has_relation`

The source types specify the actual hypotheses. See the [ALCC guide](../../docs/alcc.en.md) for execution and trust boundaries. Scientific priority is not assessed.
