---
id: CryptoHiddenScalarThresholdQuotaContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarThresholdQuotaContract.lean
novelty: not-assessed
status: reviewed
---

# Threshold transfer from a single path to recursive quotas

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarThresholdQuotaContract.lean)

## Result and exact hypotheses

`acceptance_threshold_le` proves, for a fixed adversary tape and an existing
finite `ProtocolPlan`, that single-path acceptance at least `h.value 0` implies
`protocolThresholdBound p h ≤ p.bound claim model`. The bound is computed from
thresholds, retry budgets and class-mass caps, not supplied subtree-success
assumptions. `threshold_acquisition_lower` then applies epsilon219's bound for
the actual epsilon215 collector. `threshold_positive_extracts`, when the computed
bound is strictly positive, obtains an actual schedule, a provenance-certified
fork and the epsilon214 witness-or-generator-relation extraction conclusion.

`ThresholdProfile` requires positive thresholds at every used depth, at most one,
and strictly below one whenever used as a child cutoff. The root may equal one.
At a node with parent cutoff tau and child cutoff theta the retained heavy mass
is `max(0,(tau-theta)/(1-theta))`. Multiplying it by the recursively computed child
quota bound supplies the density input to the unchanged `quota` operator.
The quotas remain 4 for IPA, 2 for eta, 3 for e. The leaf bound 1 is conditional:
a positive acceptance threshold at a deterministic leaf forces its real verifier
check to succeed. A malformed or rejected leaf cannot satisfy that premise.

`quota_profile_mono` explicitly assumes `0 ≤ p i ≤ p' i ≤ 1` for `i<n`.
Values after absorption are irrelevant. Its induction uses the existing
monotonicity in retained count; that fact does not replace the profile ranges.
`quota_density_mono` then justifies substitution of a lower density.
`threshold_average_lower` uses the heavy-prefix fraction lemma from epsilon204
and the existing average-on-heavy-set lemma. No challenge-law conditioning or
resampling only heavy calls takes place.

## Operational correspondence

`treePathEvent` is an acceptance projection of the existing epsilon220 `runIPA`.
The exact leaf/node equations retain the real packet, folded IPA statement,
reachable snapshot and each microseed occurrence. `eta_path_rate_average` and
`outer_path_rate_average` keep primitive aborts as zero branches; no child snapshot
is accessed when `query = none`. `execute_event` and `acceptance_rate_local` connect
these local events to the unchanged full single-path runner.

`continuation_rate_eq_local` and `continuation_round_eq_local` cover canonical
post-e and post-eta/round cuts. They retain a scalar-check indicator. A failed
scalar equation gives zero accepted probability even when a complete rejected
transcript and its child snapshots exist. This differs from a primitive abort.
`treeLocalAtCut` follows actual query observations; seed splitting preserves
multiplicities, including repeated calls with the same decoded value.

## Regression contract and limits

Regression fixtures use the actual acquirer and extractor. They cover a positive
F37 hierarchy (budgets 4/4/3 and class caps 1/8, 1/4, 1/32), rejected complete
transcripts, depth zero, primitive abort/wrong packet, inadequate retry budgets,
repeated microseed images, and two reachable snapshots with equal algebraic
context but different memory/history and acceptance. Flat cutoffs can give zero
conservative bound while an explicit schedule succeeds. Positive acceptance alone
need not provide enough distinct challenge classes.

The law remains epsilon219's finite independent microseed product with common
shape and a fixed budget per depth; decoders depend on exact snapshots. The
adversary tape is fixed. No unconditional positive extraction advantage follows
without positive computed bound, suitable budgets and collision margins.
No new acquirer, extractor or resource formula is introduced. External-process
refinement, random-tape averaging, ROM, polynomial complexity and hardware tests
are not established. Only scoped verification is claimed; historical full beta
baselines remain unchanged. Mathematical novelty is not assessed.
