# Release v0.7.17 — IPA Pedersen opening consistency

Epsilon212: CryptoBulletproofsIPAPedersenOpeningConsistencyContract.
212 direct MasterSuite imports; 256 formal Lean sources including Verification.lean,
byte-identical to source snapshot 6ca79cd74cded1667e788b3623f38a14d3cbbc44.
Lake remains 0.7.1; the annotated Git tag carries the release version.

## Exact statement and composition

CommittedClaim contains the vector bases G,H, generator U, value/blinding generators
B,Hblind, vector commitment Q and scalar commitment V. It contains no scalar opening.
The scalar field is ZMod q for prime q; the commitment space is an additive module.
No generator independence, finite group size, bijective masking or hardness premise
is needed for the algebraic composition theorem.

ForkBundle supplies two Pedersen opening transcripts and two IPA trees. OpeningValid
requires the same V and announcement, two verified response equations, and distinct
opening challenges e0,e1 (either individually may be zero). The existing extractor gives

    c* = (zc0-zc1)/(e0-e1), r* = (zr0-zr1)/(e0-e1).

ValidBundle checks both IPA trees at PublicClaim(Q,c*) with distinct unit outer
challenges eta0,eta1 and computed contexts Q+c*(eta_i U). Internal four-way forks
retain their distinct-square requirements. The desired dot-product equation is
not assumed as a premise.

bundle_extraction_soundness proves either a joint witness a,b,c*,r* satisfying

    Q = MSM(a,G)+MSM(b,H), dot(a,b)=c*, V=c* B+r* Hblind,

or explicit nonzero RelationCoefficients whose relation_eval is zero on the original
extended basis. The proof reuses scalar_soundness and pair_extraction_soundness.
liftRelation injects the IPA relation by inserting zero B and Hblind coefficients;
injectivity preserves nontriviality and liftRelation_eval preserves evaluation.
No generator relation is inferred from a mere mismatch of unrelated scalars.

checkedBundle validates the opening fork before checking the IPA contexts at c*.
checkedBundle_success_iff and checkedBundle_sound characterize accepted results.
checkedBundle_honest proves exact recovery of a,b,dot(a,b),r at every depth for
honest common-mask responses, distinct opening/outer challenges and four distinct
internal challenge squares.

## Regressions and epistemic boundaries

Honest depth1/2 examples over F101 exercise 4/16 leaves, including opening challenge0.
At depth0 over F5 the epsilon211 countermodel returns a nonzero relation, embedded
with zero Pedersen coefficients. Another valid opening of the SAME V may extract
a different c and fail the original IPA contexts. The relation branch does not
assert absence of every witness for the committed claim: the tested model has no
vector witness for its extracted c=1, but has another valid witness with c=0.
Checks cover altered V/Q, response/announcement/statement corruption, repeated
challenges and swapped trees. In F5^2 a nonzero blinding generator can still leave
the message exposed: nonzero alone does not imply bijectivity in arbitrary modules.

The result is deterministic algebraic composition of SUPPLIED forks after extracting
c*, not a single-transcript interactive verifier with hidden c. Perfect hiding of V
alone does not prove ZK of the whole transcript. Hiding gives no extractor, but does
not prove absolute uncomputability of r; with known c and bijective masking r is
unique. Recovering the original secret is stronger than extracting a valid opening.

Compatible-fork acquisition, adversary probability and cost, full-transcript ZK
simulation, general Forking Lemma, Fiat-Shamir/ROM, a DLog hardness reduction and
polynomial-time knowledge extraction remain outside scope. In cyclic prime-order
groups relations between generators exist; hardness concerns finding them.
Mathematical novelty remains not-assessed.

## Public verification and export

Fresh public scoped checks are separate from private evidence: strict incremental
Lake build, reviewed live unittest selection, one union transitive audit with strict
AxiomAudit, metadata, knowledge and whitespace checks. Actual metrics are recorded
in the annotated tag and release report. Allowed axioms: propext, Classical.choice,
Quot.sound. No new full beta checkpoint is claimed. The full public beta remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1).

Only the allowlisted module, integration points, addressed tests, metadata and
English documentation are exported. Private Git ancestry, Russian cards, SimLab,
Digital Brain, simulations, chats and working artifacts are excluded. No new
module index or research task is started by this release.
