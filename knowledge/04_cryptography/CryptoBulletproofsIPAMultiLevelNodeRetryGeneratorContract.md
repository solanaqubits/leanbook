---
id: CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract.lean
novelty: not-assessed
status: reviewed
---

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract.lean)

# Node-local bounded retries in recursive IPA generation

## Question, lineage and explicit model

Epsilon208's `recursive_retry_bounds` repeats an already defined whole-tree
experiment. This module instead places a retry loop inside every internal node.
Each attempt regenerates all four children, each with its own recursive budget.
It reuses epsilon208's `Source`, header validation, computed child statements and
scalar leaf checks; it does not ask the source for completed child trees.

At depth zero, a local seed supplies a proposed scalar opening, checked against
the current statement. At depth k+1, one composite attempt contains a root seed
and four independent depth-k tapes. The node tape contains budget(k+1) independent
copies of that entire composite attempt. `retry` selects the first successful
attempt or returns none. `generate` implements this recursion. A missing response,
invalid header, wrong claimed context or invalid scalar opening rejects the
selected attempt. A later attempt uses fresh coordinates for root and children.
A zero budget is allowed by the definitions and returns failure; positivity
claims require a positive budget at every internal level.

`Tape`, `tapes`, `tapes_card` and `tapes_nonempty` describe the finite product
experiment explicitly. The finite seed set C is nonempty for probability
identities. Uniform product coordinates model independence; no runtime RNG or
network delivery implementation is certified. The source remains a mathematical
parameter describing available messages and scalar proposals.

## Soundness and quantitative theorem

`generate_valid` proves that every successful result is a valid accepting tree
for its input statement. There are four children per internal node and 4^k
leaves, although the original vector dimension is 2^k. `generated_extracts` and
`extract_sound` compose with the unchanged tree extractor. Its `ResultValid`
alternative is an opening in the existing IPA interface or a nontrivial generator
relation; there is no additional blinding factor or external inner-product claim.

For a fixed root seed, its checked header determines all four child contexts.
`fixed_root_count` counts the product of the four successful child tape sets;
`attempt_rate_exact` averages the resulting products over the root seeds.
`rate_node_exact` gives the exact retry formula

    rate(k+1,s) = 1 - (1 - attemptRate(k+1,s)) ^ budget(k+1).

`node_retry_bounds` derives epsilon206's RetryBounds from this node's actual
product experiment using epsilon207. RetryBounds remains a hypothesis in the
abstract epsilon206 API. Here it is discharged separately at each internal node.

The recursive source availability contract `Dense` from epsilon208 is reused:
at a leaf, the valid-opening rate is at least b; at an internal node, a fraction
at least a of root seeds yields valid headers whose computed child contexts are
again Dense. For 0<=a,b<=1 define

    lowerBound(0)=b,
    lowerBound(k+1)=1-(1-a*lowerBound(k)^4)^budget(k+1).

`attempt_rate_lower` establishes the one-attempt bound a*lowerBound(k)^4.
`recursive_probability_lower` lifts it through the exact product retry formula.
The root-conditioned child rates need not be equal or independent of the root;
independence is used for the separate child tapes after fixing that root.
`lowerBound_bounds`, `lowerBound_mono_budget`, `lowerBound_ge_single` and
`lowerBound_positive` give range, budget comparison, comparison with epsilon208's
single-attempt bound and positivity under positive availability and budgets.

## Corrections and counterexamples

The original request inferred strict growth of actual success from a strict
lower bound between zero and one. This is insufficient: actual success may
already be one. `amplify_strict_budget` establishes strict growth of
1-(1-p)^T when the actual fixed one-attempt probability satisfies 0<p<1.
`amplify_saturated` and `lower_estimate_does_not_force_strict_actual_growth`
preserve the saturation counterexample. Lower-bound monotonicity is distinct
from strict growth of an arbitrary source's actual probability.

Reusing a single tape across retries does not generate the product experiment.
Likewise, sharing a seed across four children need not yield the product of their
success rates. A selected bad child rejects that attempt; global zero success
requires an unavoidable blocked child for every possible valid root attempt.
Availability cannot be inferred from syntax or from a positive retry budget.

Cached children cannot be accepted merely because they were valid for an earlier
context. If a new challenge or prefix changes the child statement, the existing
certificate alone proves no validity for that new statement. Reuse with equal
contexts or a separately proved validity bridge is not ruled out; it requires
a distinct caching model and proof. This contract fully regenerates children.

## Public evidence and boundaries

Public source snapshot: 04726f19649512c20623cb1acb6dce3605c0fa9e.
The annotated v0.7.14 tag and release report record checks of the public tree,
separately from private verification. Integration exposes CryptoFullSuite.ipa_node_retry.
See [release notes](../../docs/release-v0.7.14.en.md).

For every depth k, lowerBound(k) <= Pr[Success_k]; in particular the bound at
k+1 compares with success at depth k+1. `rate_mono_budget` proves monotonicity
of actual success. `rate_single_budget` proves exact equality of success rates
with epsilon208 for unit budgets. `local_retry_rate_strict` requires
0 < attemptRate < 1 and fixes the child experiment while varying this node budget.

Only propext, Classical.choice and Quot.sound are permitted. Local message and
leaf availability remains conditional. General Forking Lemma, Fiat–Shamir/ROM,
physical RNG/IO refinement, caching and polynomial runtime are not established.
Choosing practical budgets requires a separate cost and implementation model.
Mathematical novelty remains not-assessed. No new full beta is claimed.
