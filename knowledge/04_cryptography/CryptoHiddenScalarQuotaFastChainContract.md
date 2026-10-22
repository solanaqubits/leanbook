---
id: CryptoHiddenScalarQuotaFastChainContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaFastChainContract.lean
novelty: not-assessed
status: reviewed
---

# Resume chains with one fast start

Epsilon238 executes quotaResumeChainFold from startQuotaSearchFastInstrumented.
Every continuation uses the existing resumeQuotaSearchInstrumented; no cold
restart or synthesized answer-derived counters replace this execution.

Under List.IsChain (<=) (cap0::caps), fast_chain_pair_eq equates the entire
result/cost pair to one startQuotaSearchFastInstrumented at lastCap.
fast_chain_result retains the full QuotaSearchResult of the ordinary cold start,
including bound and row on exhaustion; fast_chain_toOption gives the reference
selector. All statements allow arbitrary rational profiles and tolerances.

fast_chain_success gives (found 0, (checks,inits,transitions,updates)=(1,0,0,0))
when n<=j and epsilon>=0, or j<n and epsilon>=1. This holds for any tail,
even a shrinking one, because every later result is terminal.
fast_chain_delegates, also for any tail, preserves the old executed chain's
result and adds exactly one check. fold_extra_check proves by induction that
this initial offset is carried unchanged through componentwise accumulation.
fold_found proves terminal continuations add zero costs.

With a nondecreasing chain, fast_chain_stats compares fallback to streamingStats:
only checks increase by one. fast_chain_counts gives (t+2,1,t,n*t), where t is
the selected reference budget or lastCap if no budget is found.
fast_chain_exhausted_bound fixes the exhausted cursor at lastCap.
No cold-result or cold-cost equivalence is asserted for arbitrary shrinking
chains: stored successes and larger exhausted bounds give counterexamples.

30 IO scenarios and 41 Lean examples including registry cover empty tails,
repeated bounds, immediate/intermediate success, full failure, n=0, absorption,
calibrations 4/6, negative tolerance, p=2,-1,0,1, heterogeneous profiles,
exact exhausted rows, and shrinking counterexamples. Expected rational states
are generated separately using Python Fraction before Lean regression execution.

Structural counts exclude natural control comparisons, packaging, stack,
physical allocations and rational bit complexity. No timing or memory savings
are measured. This is epsilon/scoped verification, not a new full beta.
Base: ddfb71191d6ba035d9f0037ade565c96e9c0876d. Novelty is not assessed.

[Lean](../../Verification/CryptoHiddenScalarQuotaFastChainContract.lean)
