---
id: CryptoHiddenScalarQuotaFastContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaFastContract.lean
novelty: not-assessed
status: reviewed
---

# Fast boundary branches for quota search

Epsilon233 adds chooseQuotaBudgetFastWithin. The first guard n<=j returns some0
iff 0<=epsilon, otherwise none. The second guard cap=0, with j<n, returns some0
iff 1<=epsilon. Only the remaining branch calls the existing streaming selector.
The absorbed deficit is zero; the active zero-budget deficit is one.
Both fast guards precede initial-row construction.

chooseQuotaBudgetFastWithin_eq proves exact Option equality with the reference
chooseQuotaBudgetWithin for arbitrary rational profiles, tolerances and caps.
There is no global rejection of negative epsilon: for n=1,p0=2, D(1,0)=-1,
so the regular branch can satisfy a negative tolerance.

chooseQuotaBudgetFastInstrumented reuses epsilon232 TabularStats. Fast branches
have checks=1 and inits=transitions=updates=0. The regular branch calls exactly
one epsilon231 instrumented search, preserves its checks/transitions/updates,
and adds inits=1. Result projection, fast_stats, regular_stats and the complete
stats formula are proved. For t=result.getD cap the regular tuple is (t+1,1,t,n*t).
Existing selectors and counter APIs are unchanged.

The natural-number control guards n<=j and cap=0 are excluded from deficit checks.
These are explicit source-level structural operations, not machine instructions,
allocations, physical time, memory or rational bit costs. Zero row construction
does not prove zero machine allocation. No library IsBigO or new benchmark is claimed.

extend_some preserves a selected some T when cap1<=cap2 without probability ranges.
none_iff excludes solutions only within [0,cap]. This is not deficit monotonicity:
for p0=2, D(1,0)=-1 and D(2,0)=1; the extended search still selects some1 because
that earliest feasible budget remains in the search window.

26 IO scenarios belong to the compound live test; 32 Lean examples include registry
checks. Cases cover absorption, n=0, negative tolerances, cap=0, boundaries 0/1,
nonprobability profiles, calibrations4/6, insufficient windows and old/new counters.
Verification is epsilon/scoped; full beta pins are preserved. Public export is separate.

[Lean](../../Verification/CryptoHiddenScalarQuotaFastContract.lean)
