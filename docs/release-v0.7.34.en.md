# v0.7.34 — streaming quota budget search

Source: private integration `c34325fc50b9bc6a5dd00ce14bf708bb42039213`.
Adds `CryptoHiddenScalarQuotaStreamingContract` (epsilon230), registry integration,
compact regressions and English documentation. Inventory: 232 direct MasterSuite
imports and 276 Lean sources including Verification.lean, byte-identical to source.

`chooseQuotaBudgetStreamingWithin` scans budgets 0 through cap inclusively.
It keeps the current materialized Vector row and advances with `quotaNextRow`
only after the current test fails. Zero remaining transitions still tests the
current budget. The row invariant and the interval scan specification establish
exact Option equality with `chooseQuotaBudgetWithin` for every rational profile
and tolerance. Negative tolerance, cap zero and nonmonotone profiles are included.

Success identifies the global minimum reference budget. Failure excludes only
the bounded interval. Probability ranges remain necessary for the inherited
monotone transfer to larger budgets. Reusing rows is implemented; no measured
speedup, formal complexity bound or physical collector optimality is claimed.
24 IO scenarios run within a compound live test; 31 Lean examples are counted
separately. The existing cold-cache qutrit Spec setup fix is preserved.

Independent public epsilon/scoped validation uses strict Lake, all public
unittest with live mode, catalog/integration checks and one transitive union
axiom audit. Allowed axioms: propext, Classical.choice, Quot.sound. The local
run keeps the incremental cache under an 8 GiB memory cap with swap disabled.
Lake remains 0.7.1. Full public beta remains v0.7.1,
`2419489245019fb16e32ffac641b9f88eea94126`; no new full beta run is claimed.
Private coordination, research materials, raw logs and ancestry are excluded.
