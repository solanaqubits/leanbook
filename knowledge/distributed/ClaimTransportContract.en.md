---
id: ClaimTransportContract
language: en
section: distributed
source: Verification/ClaimTransportContract.lean
source_sha256: a0a1cbefc6df61984d12792f45e3ea38e56d3736b4859935de121d7adf255af3
novelty: not-assessed
---

# ClaimTransportContract

[Section](README.md) · [Lean source](../../Verification/ClaimTransportContract.lean)

The executable finite comparator checks exact contracts after validated lists are
represented as finite sets. Contracts include full atoms (ID, text and digest),
quantities as strings, reported evidence state, evidence IDs, scope, role metadata,
non-claims, open obligations and the selected quote. Expected anchors are separate
from supplied anchors. Unknown proof references cause review, not acceptance.

`classify_preserved_iff` characterizes acceptance: valid-wire premise, equal
anchors, absent proof reference and equal contracts. `accepted_fields_equal`
projects preservation of every controlled field. `removed_premise_not_exact` and
`evidence_upgrade_not_exact` establish negative comparison properties.

For an arbitrary but **fixed** interpretation `I : Atom → Prop`,
`accepted_transport` transfers the source implication to the accepted candidate.
The more general `transport_of_inclusions` allows stronger premises and weaker
conclusions. It proves consequence, not equivalence or non-vacuity; the executable
exact mode does not accept inclusion-only changes. `atom_order_irrelevant` allows
permutations of validated atom lists.

`report_assurances_false` covers all three statuses. The model never sets semantic
equivalence, extraction completeness, kernel replay or publication authorization.
The suite is registered as `DistributedSystemsFullSuite.claim_transport`.

## Scope and assumptions

The decoder-validity flag is an external premise. JSON parsing, Python refinement,
unique-ID validation, SHA-256 computation/security, quote extraction and source
authentication are **not** proved by this module. No interpretation of natural
language is supplied, and a source theorem is an explicit argument. Reported
statuses are data, not evidence that a proof or physical claim is true.

Validation is scoped to this module, its imported project axiom closure, registry
consumers and live fixtures. No full-library verification checkpoint or scientific
novelty is asserted. The private Geek Work adapter and validator are a separate
implementation, connected by a documented specification rather than a proved
refinement.
