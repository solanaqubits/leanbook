---
id: CryptoHiddenScalarQuotaTabularContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaTabularContract.lean
novelty: not-assessed
status: reviewed
---

# Materialized quota rows and exact search equivalence

[Lean](../../Verification/CryptoHiddenScalarQuotaTabularContract.lean)

ε229 stores a row as `Vector ℚ (n + 1)` using `Vector.ofFn`, with states 0..n.
At budget zero entries below n are zero and the boundary entry is one.
`quotaNextRow` computes each entry from the same immutable previous row:
`(1-p i)*old[i] + p i*old[i+1]`; the boundary stays one. No access to n+1 occurs.
`quotaRow` iterates this transition; `quotaLowerTabular` returns one for j≥n.

`quotaRow_correct` proves the pointwise invariant by induction on the budget.
`quotaLowerTabular_eq` and `quotaDeficitTabular_eq` give exact rational value
and deficit equality with the reference recursion. No probability ranges are
assumed, and negative or greater-than-one profile values are not clamped.

`chooseQuotaBudgetTabularWithin` uses the existing inclusive `searchThrough`.
`chooseQuotaBudgetTabularWithin_eq` proves exact Option equality with ε228 for
all parameters: some, none, negative tolerance and cap zero. The existing
minimality and failure-window theorems therefore transfer; extension to larger
budgets still requires the original probability ranges. Physical collector
minimality is not implied.

The search rebuilds a row computation at each candidate budget. It does not
reuse rows across candidate budgets. No in-place update, streaming search,
bytewise identity, performance benchmark, allocation bound or complexity theorem
is claimed. A descending in-place update would incorrectly give 1/4 instead of
zero at n=2,T=1,j=0,p=1/2 by using an already updated successor.

Regressions check exact rows and rational values, absorbed states, insufficient
budgets, zero/one/heterogeneous/out-of-range profiles, inclusive cap boundaries,
negative tolerances and exact minimum budgets 4 and 6. Kernel examples are proofs;
32 IO checks exercise compiled evaluation and are not additional theorems.
Verification is scoped and preserves the previous full beta baseline. Novelty
is not assessed. Reusing rows across budgets and performance measurements are
separate future work, not results of this module.
