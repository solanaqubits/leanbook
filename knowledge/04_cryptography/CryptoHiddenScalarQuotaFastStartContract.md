---
id: CryptoHiddenScalarQuotaFastStartContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaFastStartContract.lean
novelty: not-assessed
status: reviewed
---

# Fast successful start of resumable quota search

Epsilon237 adds startQuotaSearchFast and startQuotaSearchFastInstrumented.
Absorbed n<=j with epsilon>=0, or unabsorbed j<n with epsilon>=1, returns found 0.
Every other branch delegates unchanged. Profiles may be arbitrary rational
functions; negative tolerances are not globally rejected (p=2 is a counterexample).
Existing cursor types and APIs remain unchanged.

start_found_zero proves global minimality at zero and uses minimal_selected plus
the old Option bridge; constructor elimination upgrades this to the full found 0.
Boundary lemmas compute the zero-budget deficit. startQuotaSearchFast_eq proves
unconditional equality of the full QuotaSearchResult, including retained bound,
row and proof fields. fast_exhausted_bound retains the exact cap.

Instrumentation follows execution. fast_success gives
(checks,inits,transitions,updates)=(1,0,0,0). fast_delegates adds one failed outer
rational threshold check to the old counters, counting the old repeated check at
budget zero as well. fast_delegated_counts gives (t+2,1,t,n*t), where t is the
selected budget or cap on exhaustion. startQuotaSearchFastInstrumented_result
preserves the full uninstrumented result.

Semantic continuation results transfer by rewriting, retaining all hypotheses.
Cost identities for chains do not transfer automatically: starts change inits
and checks. New chain-cost theorems are outside this module. The existing chain
predicate is List.IsChain (<=) (cap0::caps).

24 runtime scenarios and 33 Lean examples including registry projections cover
both fast successes at zero/positive caps, n=0, absorption, exact exhausted rows,
calibrations4/6, heterogeneous profiles, p=0,1,2,-1 and negative tolerances.
A counterexample shows that absorption at the queried index does not make the
whole row constant. row_correct specifies a value, not a unique evaluation method.

Counts exclude natural control guards, packaging, stack, actual allocation and
rational bit costs. Zero modeled row initializations do not prove zero machine
allocations. No new speed measurements or chain-cost theorem is claimed.
Potential use is early success while preserving the old API; application speed
requires its own measurement. Verification is epsilon/scoped, not a new full beta.

[Lean](../../Verification/CryptoHiddenScalarQuotaFastStartContract.lean)
