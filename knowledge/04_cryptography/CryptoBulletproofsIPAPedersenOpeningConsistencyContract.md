---
id: CryptoBulletproofsIPAPedersenOpeningConsistencyContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPAPedersenOpeningConsistencyContract.lean
novelty: not-assessed
status: reviewed
---

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPAPedersenOpeningConsistencyContract.lean)

# Pedersen opening consistency with two supplied IPA trees

## Specification

`CommittedClaim q A k` stores existing `Range.Generators` (G,H,U,B,Hblind), Q and V.
It contains no scalar opening. Scalars are the prime field ZMod q and A is an
additive commutative group/module; vectors have length 2^k. No finite-cardinality,
generator independence, bijective masking or hardness hypothesis is needed for
this algebraic theorem. Hiding requires its own distributional hypotheses.

`ForkBundle` supplies two linear-opening transcripts and two IPA trees with unit
outer challenges. `OpeningValid` checks the same V, the same announcement, two
correct response equations and distinct opening challenges. Individual opening
challenges need not be nonzero. `opening` reuses `extractOpening`:

    c* = (zc0-zc1)/(e0-e1), r* = (zr0-zr1)/(e0-e1).

`ValidBundle` additionally checks the two IPA trees at `publicClaim p c*`, with
distinct unit outer challenges eta0,eta1. Their statements are Q+c*(eta_i U),
with scaled generator eta_i U. The SAME extracted c* is used in both contexts.
The desired dot-product equation is a conclusion, not an input premise.

## Theorem and proof

`bundle_extraction_soundness` proves `ResultValid p (extractBundle p f)` from
`ValidBundle p f`. A witness contains a,b,c,r with all three equations:

    Q = MSM(a,G)+MSM(b,H), dot(a,b)=c, V=c B+r Hblind.

The other branch gives a nonzero existing `Range.RelationCoefficients` vector
whose `relation_eval` on the original generators is zero.
`Opening.scalar_soundness` yields the opening equation. The epsilon211 theorem
`pair_extraction_soundness` supplies the vector witness OR G,H,U relation.
`attachOpening_sound` composes these results. `liftRelation` inserts zero B and
Hblind coefficients; `liftRelation_injective` preserves nontriviality and
`liftRelation_eval` preserves evaluation. No relation is invented from a mere
mismatch between scalars of unrelated valid inputs.

`checkedBundle` checks the opening fork first, then IPA at extracted c*.
`checkedBundle_success_iff` characterizes exact accepted results;
`checkedBundle_sound` proves their validity. Rejection distinguishes invalid
opening fork from invalid IPA fork. `checkedBundle_honest` proves exact recovery
of the original a,b,dot(a,b),r at every depth for honest common-mask responses,
distinct opening/outer challenges and four distinct internal challenge squares.

## Regressions and corrections

`tests/lean/ipa_pedersen_consistency_regression.lean` checks honest depth1/2
bundles over F101, including opening challenge zero. It checks the F5 depth0
relation branch inherited from epsilon211, injected coefficients, wrong V/Q,
announcements, responses, repeated challenges, swapped trees, and an independently
valid second opening of the same V whose scalar does not match the IPA contexts.
A relation outcome does NOT rule out every possible opening of V: the countermodel
has no vector witness for the extracted c=1, but has another valid opening with c=0.
A separate F5^2 example reveals c in the second coordinate despite nonzero Hblind.
Kernel examples and runtime IO checks are separate evidence; registry regressions
check the inherited master-suite access paths. No native-decide axiom is used.

## Scope and provenance

This is OFFLINE algebraic checking of supplied forks after extracting c*, not a
single-transcript verifier for a hidden-scalar interactive protocol. A verifier
that takes public c is also not a hidden-c protocol. Perfect hiding of V alone
does not establish ZK of the combined transcript. With known c and bijective
masking r is unique; hiding does not prove its absolute uncomputability. Fork
extraction returns a valid opening, not necessarily the original secret unless
honest shared-mask hypotheses apply.

The supplied-fork acquisition, probability and computational cost, complete ZK
simulator, Fiat–Shamir/ROM, DLog hardness reduction and polynomial knowledge
extraction remain open. Novelty is
not-assessed. A potential application is an offline consistency checker for a
transcript collector; its unproved bridge is acquisition of a compatible bundle.

See [release notes](../../docs/release-v0.7.17.en.md) for the pinned source and
public verification scope. No new full-beta checkpoint is claimed.
