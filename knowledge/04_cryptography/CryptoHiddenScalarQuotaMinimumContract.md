---
id: CryptoHiddenScalarQuotaMinimumContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaMinimumContract.lean
novelty: not-assessed
status: reviewed
---

# Exact minimum budget of the reference quota

[Lean](../../Verification/CryptoHiddenScalarQuotaMinimumContract.lean)

ε228 defines `chooseQuotaBudgetWithin n p j ε cap` using the existing
ε227 `searchThrough`. It checks every natural budget from zero through cap.
A successful result gives feasibility, T₀≤cap, and strict failure of every
smaller natural budget: global minimality for the reference recursion.
Failure excludes only [0,cap]. These search properties need no probability
ranges; this selector does not reject profiles outside [0,1].

For 0≤pᵢ≤1 at i<n, j<n and a successful geometric choice K, the cap K(n−j)
is sufficient. The exact minimum is no greater; strict savings are not universal.
For ε<1 and j<n, quota_insufficient gives n−j≤T₀ without range assumptions.
With ranges, deficit feasibility at T is equivalent to T₀≤T, by budget
antitonicity. At absorption n≤j, nonnegative tolerance selects zero and
negative tolerance returns none. Negative tolerance also fails for any
probability profile.

For n=2,pᵢ=1/2, ε=2/5 selects4 rather than geometric8; ε=1/8 selects6
rather than16. The first example fails at cap3 but succeeds at cap4.
For the invalid profile p₀=2,n=1, D(1,0)=−1 and D(2,0)=1, so extension
to larger budgets requires ranges. Compact kernel and IO regressions also
cover exact equality, absorbed states, zero cap, heterogeneous profiles,
endpoint probabilities and a single quota. IO checks are not proofs.

No new collector, extractor, DP implementation or heavy exhaustive test is
introduced. Minimality concerns quotaLower, not actual acquisition success.
No polynomial-time, ROM or hardware guarantee. Scoped verification retains
the previous full beta baseline. Novelty is not assessed.
