---
id: AlgebraicCertificateSyntax
language: en
section: proof-graphs
source: Verification/AlgebraicCertificateSyntax.lean
source_sha256: bcb062358d158095dbb8b070c2f1818d3e12c365bdc84e1ab6bbbb453c2ccbb2
novelty: not-assessed
---

# Canonical ASCII JSON syntax

[Section](README.md) · [Lean source](../../Verification/AlgebraicCertificateSyntax.lean)

Defines a byte-based AST, independent parsing relation, canonical serializer and bounded parser. Proves soundness, relational uniqueness and completeness for canonical trees within explicit structural budgets. No schema validation or physical time/memory bound is implied.

## Interfaces and proof scope

- `hex`
- `escapeByte`
- `serializeString`
- `unhex`
- `readEscape`
- `readString`
- `Ascii`
- `readString_byte`
- `readString_encode`
- `JsonAST`
- `digit`
- `numberChar`
- `unsignedNumber`
- `canonicalNumber`
- `NumberBoundary`
- `escapeByte_length`
- `escaped_length`
- `unsigned_number_chars`
- `canonical_number_chars`
- `read_number_append`
- `ValueRoundTrip`
- `ArrayRoundTrip`
- `ObjectRoundTrip`
- `value_roundTrip`
- `serialize_grammar`
- `serialize_injective`
- `CanonicalParseRel`
- `maxDepth`
- `maxBytes`
- `maxNodes`
- `WithinResourceLimits`
- `parseCanonical`
- `parseCanonical_sound`
- `canonicalParse_deterministic`
- `parseCanonical_complete`
- `escapeByte_ascii`
- `string_ascii`
- `number_ascii`
- `serialize_ascii`
- `accepted_ascii`
- `accepted_byte_roundTrip`

The source types specify the actual hypotheses. See the [ALCC guide](../../docs/alcc.en.md) for execution and trust boundaries. Scientific priority is not assessed.
