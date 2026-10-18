---
id: CryptoBulletproofsIPAPartialBranchCacheResourceContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPAPartialBranchCacheResourceContract.lean
novelty: not-assessed
status: reviewed
---

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPAPartialBranchCacheResourceContract.lean)

# Partial IPA branch cache and resource comparison

## Question and corrected specification

Epsilon209 regenerates each entire parent attempt, including four children which
already have recursive retry budgets. This contract fixes a valid parent fork,
retains successful children and counts child-generator calls. The earlier exhaustive
4369-table check was finite computational evidence, not a universal proof.

The original strict-saving claim needed correction: partial success in the last
available round saves no later call. Strict saving requires a subsequently executed
round where a retained branch is skipped. A partial R=1 row costs four for both policies.

## Context safety and execution

A full Statement includes U, G, H and P, with depth fixed by its type. For an unchanged
tree already valid at its cached Statement, validity transfers exactly when the new
Statement equals that cached Statement. Different challenges or prefixes can produce
the same child Statement. Changing the computed Statement rejects the old claimed
context even if a scalar equation happens to remain true.

The cache stores four optional children. Filled slots persist; only missing slots
request another child result. Every stored tree must be valid for its fixed computed
child context. Four filled slots assemble into ValidAcceptingTree and compose with
existing tree_extraction_soundness: an IPA witness in the existing interface or a
nontrivial generator relation, without adding blinding or an external inner-product claim.

## Resource and probability statements

Both strategies use the same aligned (round,child) tape table. Reset evaluates all
four child slots in each attempted row and stops at the first fully successful row.
Cache retains successful columns and requests only missing ones, without shifting
slot indices. The common limit is R rounds and at most4R child calls, not equal
realized expenditure or an arbitrary optimal allocation of a total call budget.

Reset success is ∃r∀j success(r,j); cache success is ∀j∃r success(r,j). The first
implies the second for every table. A column's first success is no later than the
first fully successful row. Induction over rows yields costCache≤costReset≤4R.
No independence is needed for pointwise dominance or its probability consequence
under a common finite distribution.

For nonempty finite independent uniform tape coordinates and per-branch success
probabilities q_j constant across rounds, the exact probabilities are

    Pr(cache)=∏_j (1-(1-q_j)^R),
    Pr(reset)=1-(1-∏_j q_j)^R.

Cache success is at least as likely. Marginal probabilities of correlated tapes do
not justify these product identities. Child contexts are fixed before factoring;
message/opening availability remains a parameter of Source.

## Regressions, evidence and limits

For R=2, rows [success,success,failure,failure] and [failure,failure,success,success]
make reset fail after8 calls while cache succeeds after6. Independent fair Bool
cells give reset31/256 versus cache81/256. A rejected header or unavailable child
is not repaired by a cache. Concrete ZMod101 examples distinguish changed contexts
from different challenges with equal computed contexts.

Development base04726f19649512c20623cb1acb6dce3605c0fa9e. Suite exposure:
CryptoFullSuite.ipa_partial_cache. Public checks are recorded separately in the annotated v0.7.15 tag and
[release notes](../../docs/release-v0.7.15.en.md); historical checks are not new runs.
Only propext, Classical.choice and Quot.sound are allowed; no new full beta claim.

Cost counts child-generator calls in the specified execution model, not compiled
runtime, all descendant checks, preallocated entropy, memory or extractor validation.
Cache lookup/storage overhead is separate. Early-abort rows, changing parent forks,
and adaptive budget allocation require different comparisons. A possible application
is a fixed-context offline IPA collector, but its source/RNG/memoization/runtime
bridge remains unproved. No general Forking Lemma, ROM or polynomial-time claim.
Novelty is not-assessed. Private research materials are excluded from this release.

`assemble` is a structural builder, not a validator of arbitrary poisoned caches: its theorem requires `CacheValid`. `cachedGenerate` derives that invariant from child-generator outputs. External/stale trees are rejected by `checked_extract`; filled slots alone do not certify validity.

## Lean API

`valid_tree_transfer_iff`, `runCache_preserves`, `runCache_valid`, `cachedGenerate_valid`, `cachedGenerate_extracts`, `cache_cost_le_reset`, `reset_cost_le_budget`, `cacheTrace_length`, `cacheTrace_subset_reset`, `strict_saving_after_partial`, `cache_probability_dominates`, `cache_run_probability_exact`, `reset_run_probability_exact`, `cachedGenerate_probability_exact`, `mean_cache_cost_le_reset`.
