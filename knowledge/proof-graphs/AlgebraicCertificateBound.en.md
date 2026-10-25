---
id: AlgebraicCertificateBound
language: en
section: proof-graphs
source: Verification/AlgebraicCertificateBound.lean
source_sha256: 9853b522f5529512e685b88e107a7bd0064a50752328aca7b569515b0290c1c1
novelty: not-assessed
---

# Binding to the supplied passport

[Section](README.md) · [Lean source](../../Verification/AlgebraicCertificateBound.lean)

Checks the lowercase hexadecimal SHA-256 of the canonical passport body with problem_id removed, and certificate/passport identifier equality. BoundTaskRel existentially connects both ASTs, schema and binding. The caller must independently choose and authenticate the expected passport; a self-consistent pair is not evidence of that authority.

## Interfaces and proof scope

- `removeProblemId`
- `problemId`
- `passportBody`
- `canonicalObject_iff`
- `canonicalObject_filter`
- `removeProblemId_canonical`
- `PassportHashValid`
- `BindingRel`
- `BoundTaskRel`
- `bindingCheck`
- `bindingCheck_iff`
- `decodeBoundTask`
- `decodeBoundTask_success_iff`
- `decodeBoundTask_sound`
- `boundTaskRel_unbound`
- `boundTaskRel_deterministic`
- `boundTaskRel_digest`
- `accepted_has_relation`

The source types specify the actual hypotheses. See the [ALCC guide](../../docs/alcc.en.md) for execution and trust boundaries. Scientific priority is not assessed.
