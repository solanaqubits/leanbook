---
id: CryptoHiddenScalarQuotaStreamingContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaStreamingContract.lean
novelty: not-assessed
status: reviewed
---

# Streaming search with reusable quota rows

ε230 scans budgets 0 through cap inclusively. `quotaStreamingScan` receives the
current budget, a materialized `Vector ℚ (n+1)` and the number of remaining
transitions. It tests the current row first, including when fuel is zero, and
returns immediately on success. Otherwise it advances through `quotaNextRow`.
Each transition reads the same immutable previous row; earlier rows are not
recomputed by the search. `quotaRowValue` returns one for every state j≥n.

`quotaStreamingScan_row_step` preserves row = quotaRow n p T at each transition.
`quotaStreamingScan_spec` proves the first feasible budget on [T,T+fuel], or
failure at every budget in that interval. The initial row is quotaInitialRow n.
`chooseQuotaBudgetStreamingWithin_eq` identifies the exact Option result with
chooseQuotaBudgetWithin for all rational profiles, tolerances and natural caps.
It uses the specifications of both searches and uniqueness of the first feasible
budget, without monotonicity or probability-range assumptions.

Thus some T is globally minimal for the reference recursion, while none only
excludes budgets in [0,cap]. Extension of feasibility to larger budgets still
needs the probability ranges required by the existing ε228 theorem. In
particular p₀=2, n=1, ε=-1 returns some 1 even though budget 2 fails again.
The equality concerns returned mathematical values, not representation bytes,
physical collector optimality, runtime, allocation, or asymptotic complexity.

Compact regressions include absorption, cap zero, insufficient windows, exact
boundary acceptance, profiles 0/1/negative/greater than one/heterogeneous,
minimum budgets 4 and 6, and continuation from a nonzero valid row. There are
24 runtime checks within the compound live test; kernel examples are separate.
Verification is epsilon/scoped; previous full beta baselines remain unchanged.
Novelty is not assessed. Benchmarks and complexity proofs are separate work.

[Lean](../../Verification/CryptoHiddenScalarQuotaStreamingContract.lean)
