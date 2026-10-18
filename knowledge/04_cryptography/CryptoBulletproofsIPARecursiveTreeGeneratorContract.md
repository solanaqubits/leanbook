---
id: CryptoBulletproofsIPARecursiveTreeGeneratorContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPARecursiveTreeGeneratorContract.lean
source_sha256: 89b2d921e34cad1ea485a2983bd55c96bd939deadb6dc3eb14cf7577c160556a
novelty: not-assessed
status: reviewed
---

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPARecursiveTreeGeneratorContract.lean)

# Recursive finite IPA tree generation

## Question and explicit inputs

Epsilon207 checks supplied completed child trees. This module recursively builds
children from a Source of messages and proposed scalar openings. Source.leaf takes
the computed scalar Statement and a local seed, returning an optional claimed
Statement and scalars a,b. Source.node takes depth, computed Statement and seed,
returning an optional claimed Statement, common message (L,R) and four challenges.
It never takes a completed child tree. Prime q, a ZMod q module and decidable group
equality are required. The source is a mathematical parameter, not a proved
implementation of an arbitrary adversary or an algorithm discovering openings.

header rejects missing messages, a wrong claimed context, zero challenges or equal
squares. generate at depth zero checks the claimed context and
P = a•G(0) + b•H(0) + (a*b)•U. At depth k+1 it computes child_statement from the
parent, common message and each challenge; it recursively generates all four
children on their separate tapes. collect rejects any missing child. No default
valid child is invented. generate_valid proves full ValidAcceptingTree, while
leafCount_eq proves 4^k leaves (vector length is 2^k, a different quantity).

## Finite experiment and proof

Tape Omega 0=Omega; Tape Omega (k+1)=Omega × (Fin 4 -> Tape Omega k).
tapes C k enumerates the complete product of local seeds in finite C, with uniform
mass. tapes_card is |C|^checkCount(k), where checkCount(0)=1 and
checkCount(k+1)=1+4*checkCount(k). Duplicate representations are not weighted twice.
good filters actual successful generate outcomes; rate=|good|/|tapes|.

Fixing a root seed determines its header and all child contexts. fixed_root_count
identifies the successful child tuples with a product of four filtered child tape
sets. good_node_count sums these products over root seeds. rate_node_exact proves:

rate(s,k+1) = (1/|C|) sum_(w in C) rootRate(s,w),

where rootRate is zero for a rejected header and otherwise the product of the four
child rates in the contexts computed from this exact header. These rates may vary
with the root. No multiplication of unconditional marginal probabilities is used.

rate_node_lower gives (|B|/|C|)*b^4 when B is a subset of root seeds with valid
headers and every corresponding child rate is at least b>=0. C must be nonempty.
Dense makes local availability recursive: leaf rate at least b; at least fraction
a of root seeds have valid headers and Dense children in their computed contexts.
recursive_probability_lower proves lowerBound(0)=b,
lowerBound(k+1)=a*lowerBound(k)^4 for a,b>=0. For positive a,b, dense_extracts
constructs an accepting outcome and a valid extraction result. Recursion alone
provides no positivity: a missing required response can annihilate the rate.

rate_zero_of_blocked_child requires a zero-rate child for EACH valid root seed.
One malformed leaf only rejects tapes selecting it; it does not automatically
make the whole experiment impossible. This corrects the overly broad reading of
the original regression request without weakening the intended failure checks.

## Composition and regressions

generated_extracts and extract_sound call CryptoBulletproofsTreeExtraction without
changing its API: ResultValid means an opening of the existing IPA commitment OR
a nontrivial relation among its generators. There is no added blind or separate
external inner-product equality. recursive_retry_bounds applies epsilon207's
product theorem to independent whole-tree tapes; epsilon206 still has a general
conditional RetryBounds interface.

Regression sources use nonzero generators and explicit scalar proposals. Depths1
and2 succeed and validate4 and16 leaves. A bad selected leaf, wrong scalar, wrong
claimed context, missing response, zero challenge and opposite challenges fail.
A root message changing the child commitment is accepted as a header but the old
scalar responses fail in the newly computed contexts. A nonzero scalar opening
is tested separately. A concrete Dense witness is proved, not only assumed.

With Boolean leaf seeds and an always-valid root, depth1 rate is1/16 on32 tapes.
Reusing one Boolean for all children gives1/2, not1/16. The full depth2 domain has
2097152 tapes by a cardinality theorem; this large space is not enumerated in tests.
A singleton seed domain exercises depth2 generation and extraction directly.

## Public verification and boundaries

Public-tree evidence is recorded separately in the annotated v0.7.13 tag and
release report. Source snapshot: 4ea630adc474c8547f281db210e59234fed398ca.
Only propext, Classical.choice and Quot.sound are allowed. Novelty is not assessed.
See [release notes](../../docs/release-v0.7.13.en.md).

RetryBounds is derived for the concrete independent product experiment; it remains
a premise in the general epsilon206 interface. Recursive Source message/scalar
availability is conditional, not guaranteed for an arbitrary prover. Actual RNG,
IO, strategy access, memory and operation costs require separate refinement.
No general Forking Lemma, adaptive rewind, Fiat–Shamir/ROM or polynomial runtime
claim follows from these finite algebraic and counting results.
