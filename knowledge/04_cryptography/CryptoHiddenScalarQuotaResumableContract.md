---
id: CryptoHiddenScalarQuotaResumableContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaResumableContract.lean
novelty: not-assessed
status: reviewed
---

# Resumable minimum quota budget search

Epsilon234 adds QuotaSearchCursor, QuotaSearchResult, initQuotaSearch,
startQuotaSearch and resumeQuotaSearch. Semantic equalities hold for arbitrary
rational profiles and tolerances, without probability ranges. Existing selectors
and the extractor are unchanged.

A cursor stores bound, the retained Vector of length n+1, row=quotaRow n p bound,
and failure of every budget t<=bound. Parameters n,p,j,epsilon stay fixed.
A correct row alone does not certify global minimality. Proof fields do not
execute a fresh prefix search when resumed.

Results are found T or exhausted cursor. The found constructor carries data,
not a minimality proof. IsMinimalQuotaBudget states D(T)<=epsilon and failure
of all smaller budgets. ResultCorrect cap requires a minimal found T<=cap,
or an exhausted historical bound>=cap; cursor invariants are already in its type.

quotaResumableScan checks the current row even at zero fuel, advances via
quotaNextRow only after failure with remaining fuel, and returns the actual
last row on exhaustion instead of rebuilding it from zero. Its Option projection
equals quotaStreamingScan. Correctness and exact exhausted bound T+fuel are proved.
startQuotaSearch checks [0,cap]; initQuotaSearch is the zero-cap start.
startQuotaSearch_bound proves the initial exhausted bound equals cap.

resumeQuotaSearch always preserves found T. For exhausted c it returns c unchanged
when newCap<=c.bound, otherwise performs one row transition and scans
[c.bound+1,newCap]. The covered-window branch performs no deficit checks or row
transitions, but executes the natural-number control guard. On exhaustion,
resume_exhausted_bound gives bound'=max(c.bound,newCap).

resume_exhausted_eq holds for every newCap. Under IsMinimalQuotaBudget,
resume_found_eq_iff characterizes equality with the cold selector by T<=newCap.
resume_start_eq and resume_twice_eq require nondecreasing caps. Shrinking after
success is not covered: n=1,p=1,j=0,epsilon=0,cap1=1,cap2=0 retains some1 while
the cold zero-cap search gives none. Negative tolerance is not globally rejected:
p0=2 can succeed at budget1.

32 IO scenarios run inside the compound live test; 40 Lean examples include
registry checks. Cases cover initialization, absorption, negative tolerances,
calibrations4/6, exact retained rows, covered windows, repeated extensions,
nonprobability profiles, terminal found and the shrinking counterexample.
A forged found99 illustrates why separate minimality assumptions are necessary.

Verification is epsilon/scoped. New cost counters, benchmarks, serialization,
external cursor authentication, machine allocations and bit complexity are outside
scope. Minimality concerns the reference recursion, not physical acquisition.
Full beta pins are preserved; public export is separate.

[Lean](../../Verification/CryptoHiddenScalarQuotaResumableContract.lean)
