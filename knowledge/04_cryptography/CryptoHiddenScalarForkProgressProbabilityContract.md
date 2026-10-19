---
id: CryptoHiddenScalarForkProgressProbabilityContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarForkProgressProbabilityContract.lean
novelty: not-assessed
status: reviewed
---

# Probability of accumulating retained fork branches

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarForkProgressProbabilityContract.lean)

## Actual collector and hypotheses

`retainedCount` counts values saved by prefixes of the existing epsilon215 `scan`.
It starts at zero, is bounded by quota n, and each additional candidate leaves it
unchanged or increases it by one. Success is absorbing. Failed candidates may be
retried with new child schedules; only keys of retained successes block insertion.
`KeyCoherent` requires the successful value's key to equal its candidate label.
`scan_invariants` proves distinct retained keys, and `collect_success_iff_quota`
connects the actual collector's result to reaching n. Without coherence, reaching
list length n need not pass the final distinct-key selection.

Fix a nonempty finite set D of uniformly sampled seeds, each specifying a schedule
of length T. `CountLaws` describes the retained-count process N. `ProgressBounds`
requires rates 0 ≤ p(j) ≤ 1 and, for every i < T and j < n,

    p(j) · |{w ∈ D : N(i,w)=j}|
      ≤ |{w ∈ D : N(i,w)=j and N(i+1,w)=j+1}|.

This is a conditional progress bound, written without division so empty fibers
cause no problem. Independent draws and a Markov actual process are not assumed.
Marginal acceptance alone is insufficient. Full-history lower bounds can justify
these hypotheses by aggregation, but this module does not infer them for an
arbitrary adversary. Arbitrary real-valued probability measures are not modeled;
the formal result uses rational probabilities of finite uniform seed sets.

## Universal quota theorem

`quotaLower n p b j` is a reference recurrence: H(0,j) is the indicator j ≥ n;
H(b+1,j)=1 if j ≥ n, otherwise

    (1-p(j)) H(b,j) + p(j) H(b,j+1).

`quota_step_mono` proves monotonicity in the retained count without requiring
monotone rates. Finite sums of the corresponding potential yield
`quota_probability_lower`: H(T,0) ≤ Pr[N(T)=n]. `collect_probability_lower`
applies this to the actual scan. The bound permits unsuccessful attempts and
successful retries, unlike a bound counting only rejection-free schedules.
`quota_one` recovers 1-(1-p(0))^T; `quota_insufficient` handles budgets below quota.

`unblocked_probability_lower` gives max(0,d-blocked) after removing already saved
classes. The success and blocked events must belong to the same conditional
finite experiment. Child-subtree success density remains an explicit premise.

## Snapshot adapters and extraction

`roundAttempt` and `etaAttempt` name the existing collector's candidate operations;
they do not introduce a replacement search algorithm. Exact event equalities and
key-coherence proofs connect them to `acquireTree`, `acquireNode` and
`acquireCompressedFork`. The three probability adapters use quotas 4 (distinct
nonzero squares), 2 (distinct unit eta calls), and 3 (distinct outer e calls).
Each uses the exact reachable snapshot, one fixed adversary tape and its own
explicit `ProgressBounds`. The node adapter assumes the actual observed scalar
response and its checked Pedersen equation; the outer adapter assumes a valid
initial announcement. It makes no positive-bound claim for initial abort.

`positive_progress_extracts` composes a positive outer bound with epsilon215:
there exists an actual sampled schedule producing a provenance-certified fork
and the epsilon214 witness-or-generator-relation extraction result.

## Resources, regression and boundaries

T counts local candidate probes, not adversary queries, restores or machine time.
The epsilon215 `ResourceTrace` and schedule upper bounds remain applicable.
Q(k)=4+2(4^(k+1)-1), R(k)=Q(k)-1 are exact only for clean successful traversals;
initial abort has Q=1,R=0. No new exact-cost formula for arbitrary retries is claimed.

Regressions compare success mass 1/2 with clean mass 1/4, reject an unjustified
independence estimate for correlated repeats, test inconsistent keys and blocked
mass, and compose actual depth-one F11 acquisition with retries and extraction.

No global-acceptance-to-local-density theorem, general Bellare–Neven lemma,
external-process refinement, ROM/Fiat–Shamir or polynomial runtime guarantee is
claimed. All provenance is relative to the existing snapshot execution model.
