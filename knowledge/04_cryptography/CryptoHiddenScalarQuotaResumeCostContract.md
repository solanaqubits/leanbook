---
id: CryptoHiddenScalarQuotaResumeCostContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaResumeCostContract.lean
novelty: not-assessed
status: reviewed
---

# Exact costs of resumable quota search

Epsilon235 instruments the actual branches of epsilon234 resumption.
quotaResumableInstrumentedScan uses epsilon231 quotaNextRowCounted, summing
active-update annotations of materialized entries. Executable counters are not
synthesized from the final answer. scan_result proves full QuotaSearchResult
equality, including the exhausted cursor bound and row. scan_stats connects
the scan counters to the existing epsilon231 instrumented scan.

startQuotaSearchInstrumented and resumeQuotaSearchInstrumented return
QuotaSearchResult paired with TabularStats. Field order is checks, inits,
transitions, updates; updates counts active cells. start_result and resume_result
hold for all rational profiles and tolerances without probability ranges.
Terminal found values are preserved even without minimality certificates;
cold-search equality separately requires genuine minimality and T<=newCap.

A start counts one row initialization. With t equal to the found budget or the
cap on failure, start_counts gives (t+1,1,t,n*t). start_cold_stats equals the
existing epsilon232 streamingStats, which adds one initialization to epsilon231
SearchStats without changing that old API.

Resuming found T has zero counters. Resuming exhausted c at newCap<=c.bound
returns the same cursor and zero counters. For a larger cap, one counted row
transition precedes the first new deficit check. Success at T>b=c.bound costs
(T-b,0,T-b,n*(T-b)), with b<T<=newCap. Exhaustion costs
(newCap-b,0,newCap-b,n*(newCap-b)). resume_exhausted_counts unifies all exhausted
input cases using truncated natural subtraction; resume_success_counts and
resume_failure_counts provide explicit outcome forms.

twoStageQuotaSearchInstrumented adds the four counters of its executed stages.
two_stage_result preserves the full resume(start(...),...) result.
two_stage_additive requires cap1<=cap2 and equates the entire cost structure
with cold streamingStats at cap2. Thus splitting the window adds no operations
in these four counters. Natural-number guards, data packaging, stack, machine
instructions, allocations and rational bit costs are excluded. No benchmark,
serialization or physical complexity claim is made.

30 IO scenarios run inside the compound live test; 38 Lean examples include
registry checks. Cases cover early/later success, calibrations4/6, exhaustion,
equal/zero windows, absorption, n=0, negative tolerance, arbitrary profiles,
terminal found99 and retained rows. Shrinking after exhaustion and after success
provide counterexamples to universal cost equality with a smaller cold window.
Old selectors and the extractor remain unchanged. Verification is epsilon/scoped;
full beta baselines remain unchanged and public export is separate.

[Lean](../../Verification/CryptoHiddenScalarQuotaResumeCostContract.lean)
