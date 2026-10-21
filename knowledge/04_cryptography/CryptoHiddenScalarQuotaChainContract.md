---
id: CryptoHiddenScalarQuotaChainContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaChainContract.lean
novelty: not-assessed
status: reviewed
---

# Finite chains of resumable quota search

Epsilon236 proves full state and structural cost equality between a finite
nondecreasing resumption chain and one cold start at the final cap.

cursor_ext identifies cursors with equal bounds: row_correct fixes the same
quotaRow, and proof fields are identified by proof irrelevance.
resumeQuotaSearch_startQuotaSearch strengthens the old Option-only bridge to
full QuotaSearchResult equality under a<=b. Exact exhausted bounds matter:
startQuotaSearch_bound and resume_exhausted_bound give max a b=b.
ResultCorrect alone allows a historical horizon larger than the current cap.

lastCap cap0 caps takes getLast of the nonempty cap0::caps; an empty tail gives
cap0. This library calls the adjacent-chain condition List.IsChain (fun a b =>
a<=b) (cap0::caps), corresponding to the project's proposed List.Chain notation.
quotaResumeChainStep actually calls resumeQuotaSearchInstrumented and adds
its four counters through TabularStats.add. quotaResumeChainFold retains the
actual result while processing caps left to right. runQuotaResumeChainInstrumented
starts once; an empty tail means one start, not no search.

chain_pair_eq is one pair invariant: under nondecreasing caps the output equals
(startQuotaSearch ... lastCap, streamingStats ... lastCap).
chain_fold_cold inducts once on the tail; chain_step_cold uses the full-result
bridge and epsilon235 two_stage_additive. chain_result, chain_toOption and
chain_stats are projections. chain_counts gives (checks,inits,transitions,updates)
=(t+1,1,t,n*t), where t is the found budget or final cap on failure.
streamingStats is the epsilon232 adapter adding one initialization to epsilon231.
Parameters n,p,j,epsilon remain fixed throughout; arbitrary rational profiles
and tolerances are allowed without probability ranges.

32 IO scenarios run inside the compound live test; 40 kernel examples include
registry checks. Cases cover empty tails, repeated caps, early/intermediate
success, exact exhausted cursors, calibrations4/6, n=0, absorption, negative
tolerances and outside-range profiles. Shrinking after success and exhaustion
refutes a universal theorem without monotonicity; not every nonmonotone chain
is asserted to violate equality.

Guards, packaging, stack, machine instructions, physical allocations and rational
bit costs are excluded. No benchmarks, serialization or external cursor validation.
Old APIs remain unchanged; epsilon/scoped verification does not refresh full beta.

[Lean](../../Verification/CryptoHiddenScalarQuotaChainContract.lean)
