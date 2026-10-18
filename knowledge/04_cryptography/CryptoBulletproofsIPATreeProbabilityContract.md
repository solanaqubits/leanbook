---
id: CryptoBulletproofsIPATreeProbabilityContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPATreeProbabilityContract.lean
source_sha256: cd7d2b4d70d96d545500c3e94b58a50d1edea2c01fc0a5cafd1ccae90a2da9bd
novelty: not-assessed
status: reviewed
---

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPATreeProbabilityContract.lean)

# Finite probability of a complete IPA tree

## Question, model, and corrections

The user asks to lift epsilon204's one-node probability to a complete extraction
tree. The existing transcript tree has four children per internal node and 4^k
scalar leaves; vector length is 2^k. Seven accepting calls is a sufficient
acquisition criterion, not part of tree validity: four nonzero distinct-square
challenges suffice. k=0 checks a scalar leaf; k=1 checks one fork and four leaves.

A finite nonempty set C contains equally likely random tapes. A function
`generate` maps each tape to a complete candidate IPATranscriptTree. The same
tape may correlate all prefixes, siblings and levels. This is a prescribed finite
experiment, not a model of an implemented rewind algorithm. Repeated outputs
retain their multiplicity through distinct tapes. `probability C E` is
|E intersection C| / |C| over the rationals.

`localChecks` traverses a candidate in preorder. It checks the claimed context,
nonzero challenges, distinct squares and every scalar leaf, passing the computed
child_statement rather than trusting a claimed child context. A failed nonzero
guard produces a fixed-length rejecting check list. `checkCount` is 1 at depth0
and 1+4*checkCount k at the next depth. `localChecks_length` and
`localChecks_valid` prove the check count and equivalence with ValidAcceptingTree.
`treeTests` turns these checks into functions on the common tape space.

## Exact conditional hypothesis and proof

Let E0=C and E(i+1) consist of tapes in Ei that pass test i.
`ConditionalBounds C tests bs` requires matching lengths and, at each step,
0<=b_i<=1 and b_i*|Ei|<=|E(i+1)|. When Ei is nonempty,
`conditional_step_iff` identifies this with b_i <= Pr[test i passes | Ei].
On a zero-mass prefix the multiplicative inequality remains meaningful; no
positive conditional probability is inferred from division by zero.

The condition includes ALL previous successful tests, including earlier siblings,
not just ancestors. Independence is not required. The false ancestor-only product
is refuted by two siblings w and not w on a uniform bit: each has probability1/2
under an always-valid root, yet their intersection is empty.

`sequential_count_lower` multiplies successive cardinality inequalities using
nonnegative tail products; induction gives |En| >= |C|*product b_i.
`sequential_probability_lower` divides by the positive |C|.
`passing_treeTests` identifies En with `validOutcomes` exactly.
`tree_probability_lower` gives Pr[complete valid tree] >= product b_i;
`tree_uniform_lower` specializes to p^(checkCount k). This bound includes leaf
checks. No algorithm for obtaining the conditional bounds is assumed or proved.

`extractor_event_eq` identifies the entire success event with checked_extract
acceptance. `generated_tree_extracts` gives a valid extraction result on every
successful tape. Positive product yields an actual tape and
`conditional_tree_dichotomy`: a witness in the existing IPA target equation OR
an explicit nonzero relation among the original generators. It need not be the
prover's original private witness.

`four_draw_tree_probability_lower` connects to epsilon204's exact four-draw
sample space: with independently context-validated completed child responses,
its root probability is a lower bound for the generated complete tree. At k=0
those responses are scalar leaves. Without that child premise the one-node
bound does not certify a full tree.

## Regressions and limits

The depth-two fixture uses16leaves and21checks: one bad last leaf on half the
tapes gives exact success probability1/2 and conditional factors twenty1s then1/2.
Other regressions cover disjoint/correlated siblings, zero-mass prefixes, malformed
factor lists, context substitution, duplicate/zero calls and incomplete draws.
Four calls {1,2,3,4} give exact probability3/32; adding a rejected fifth call
reduces it to24/625. Thus shrinking C at fixed A can INCREASE success; no general
monotonic degradation with field size is claimed. The same-cardinality set
{1,-1,2,-2} has only two square classes and gives zero success.

The finite conditional theorem is proved under explicit per-prefix inequalities.
It does not show these inequalities hold for an arbitrary adversary or a real
rewind implementation. Adaptive oracle queries, general Forking Lemma,
Fiat–Shamir/ROM security, expected polynomial time, binding, blinding and external
public dot-product claims remain open. Tests of a degenerate zero-generator
fixture do not establish computational binding. No physical claim is made.

## Evidence

Public-tree validation is recorded separately in the annotated v0.7.12 tag and
release report. Source snapshot: 602369e67aa3f38fba4bc011b058d36b12a7df2e.
Only propext, Classical.choice and Quot.sound are allowed. Novelty is not assessed.
See [release notes](../../docs/release-v0.7.12.en.md).

Additional finite-field regression: all nonzero calls in ZMod7 give zero fork
probability (three square classes); ZMod11 has ten nonzero calls and strictly
positive probability by epsilon204. This comparison changes both field and call set.
