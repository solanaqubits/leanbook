# v0.7.32 — exact minimum reference quota budgets

Source: private integration `27116c2b5b957119c886025a2118fe08c23a1960`.
The public export adds `CryptoHiddenScalarQuotaMinimumContract` (epsilon228),
its registry wiring, compact regressions and English documentation.
Target inventory:230 direct MasterSuite imports and274 formal Lean sources,
including Verification.lean, byte-identical to the pinned source.

`chooseQuotaBudgetWithin` reuses `searchThrough` to check every natural budget
from zero through cap inclusively. A successful result is globally minimal for
the reference recursion quotaLower. Failure excludes only the finite window.
Pure search correctness and the insufficient-time lower bound need no probability
ranges. Ranges0<=p_i<=1 are required for the sufficient geometric cap and for
extension to every larger budget. Absorption selects zero only for nonnegative
tolerance. No minimum actual collector budget, DP implementation or new extractor.

For n=2,p=1/2, tolerance2/5 selects4 instead of the geometric8; tolerance1/8
selects6 instead of16. Compact kernel examples and25 IO scenarios cover these
comparisons, exact hits, deficient caps, endpoint and heterogeneous profiles,
absorption, negative tolerance and the invalid-profile monotonicity counterexample.
The IO scenarios belong to a compound live test, not25 additional unittests.

Verification is independent public epsilon/scoped: strict Lake build, all public
unittest modules with live mode, catalog/integration checks, and one transitive
union axiom audit. Only propext, Classical.choice and Quot.sound are allowed.
Checks retain the build cache and run under an8GiB memory limit.

Lake remains0.7.1. The last full public beta basis remains v0.7.1,
`2419489245019fb16e32ffac641b9f88eea94126`. This release is not a fresh full beta
checkpoint. Private coordination, research cards, logs and ancestry are excluded.
