# Release v0.7.15 — IPA partial branch cache and resource comparison

Epsilon210: CryptoBulletproofsIPAPartialBranchCacheResourceContract.
210 direct MasterSuite imports; 254 formal Lean sources including Verification.lean,
byte-identical to private snapshot c65e15ac82e49c2c9185430d2cdbae809a503c44.
Lake remains 0.7.1; the annotated Git tag carries the release version.

## Context safety and extraction

The contract fixes a valid parent fork and retains successful children in four
optional slots. An unchanged tree already valid at its cached Statement transfers
exactly when its full computed child Statement matches. Challenge or prefix syntax
alone is not the key: distinct inputs can compute identical contexts. Depth is fixed
by the type. Filled slots alone do not certify arbitrary trees: assemble requires
CacheValid, cachedGenerate derives it from checked child-generator outputs, and
checked_extract rejects stale or invalid trees.

A completely filled valid cache assembles a ValidAcceptingTree and feeds the existing
tree extractor. The result is an IPA witness in the current interface OR a nontrivial
generator relation. This adds neither blinding nor an external inner-product claim.

## Equal limits, exact costs and finite probabilities

Both policies share an aligned (round,child) tape table and a fixed valid parent fork.
Reset evaluates all four children of each attempted row, stopping at the first fully
successful row. Cache calls only missing slots and keeps slot coordinates unchanged.
The common limit is R rounds and at most 4R child calls, not equal realized expense
or an arbitrary optimal allocation of a total budget.

For every table, reset success (exists r, forall j) implies cache success (forall j,
exists r), and costCache <= costReset <= 4R. The emitted call traces refine these
counts. Event inclusion gives probability dominance on a common finite sample space
without requiring independence. A partial success in the final available round
alone does not save calls; strict savings requires a later skipped call.

For nonempty finite independent uniform coordinates, with each branch's success
probability q_j constant across rounds:

    Pr(cache success) = product_j (1 - (1 - q_j)^R),
    Pr(reset success) = 1 - (1 - product_j q_j)^R.

The first is at least the second. Correlated marginals do not establish these exact
identities. For two complementary partially successful rows, cache succeeds with
6 calls while reset fails after 8. Independent fair Boolean cells at R=2 give
81/256 for cache versus 31/256 for reset. The concrete generator/extractor bridge
and context-collision counterexamples are included in Lean regressions.

## Boundaries and public verification

Cost counts scheduled child-generator calls in the stated execution model, not
compiled runtime, all descendant checks, preallocated random entropy, cache storage
or extractor validation. Early-abort reset rows, changing parent forks and adaptive
budget allocation require separate models. Message and leaf-opening availability
remains conditional. General Forking Lemma, Fiat–Shamir/ROM, physical RNG refinement
and asymptotic polynomial runtime are not established. Novelty is not-assessed.

Public scoped checks are separate from private evidence: strict incremental Lake
build, reviewed live unittest selection, one union transitive audit with strict
AxiomAudit, metadata, knowledge and whitespace checks. Actual metrics appear in the
annotated tag and release report. Allowed axioms are propext, Classical.choice,
Quot.sound. No new full beta is claimed: public basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1), private basis remains
090aed141b831aee5182197e9ea205176f361c0f.

Russian cards, SimLab, Digital Brain, source chats, simulations, private working
materials and private Git ancestry are excluded. No new module index is allocated.
