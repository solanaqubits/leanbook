# v0.7.33 — materialized quota rows and exact search equivalence

Source: private integration `befc0cb4e09a4d713b5de3ec1b74461f9c5596ff`.
The public export adds `CryptoHiddenScalarQuotaTabularContract` (epsilon229),
registry integration, compact regressions and English documentation.
Inventory: 231 direct MasterSuite imports and 275 Lean sources including
Verification.lean, byte-identical to the pinned private source.

`quotaInitialRow` and `quotaNextRow` materialize `Vector Q (n+1)` rows.
The row invariant, scalar adapter and deficit exactly equal `quotaLower`
for all rational profiles. The search adapter has identical `Option Nat`
results to `chooseQuotaBudgetWithin`, including failure, negative tolerances
and cap zero. Probability ranges are unnecessary for these equalities;
inherited monotonicity and probability interpretations retain their premises.

Every transition reads the same immutable previous row. The search rebuilds
rows for each candidate budget. Streaming reuse, in-place mutation, performance
measurements, complexity bounds and physical collector minimality are excluded.
32 executable scenarios run within one compound live test. Kernel examples
also cover row initialization, absorption, invalid probability profiles and
the incorrect descending in-place update counterexample.

This release includes the qutrit cold-cache test fix from public commit
`03baade5798d0a8dcde1ae45911accc189bf5c2a`: explicitly build the pinned decoder
Spec before the regression instead of depending on another test's cached build.
Historical tags retain their original bytes and CI results. The fixed commit's
[GitHub Actions run](https://github.com/solanaqubits/leanbook/actions/runs/39479677546)
passed; the new release has its own independent checks and workflow runs.

Verification is public epsilon/scoped: strict Lake build, all public unittest
with live mode, catalog/integration checks and one transitive union axiom audit.
Only propext, Classical.choice and Quot.sound are allowed. The local verification
retains the incremental cache and runs with an 8 GiB memory limit.
Lake remains 0.7.1. The full public beta remains v0.7.1,
`2419489245019fb16e32ffac641b9f88eea94126`; no new full beta checkpoint is claimed.
Private coordination, research materials, raw logs and ancestry are excluded.
