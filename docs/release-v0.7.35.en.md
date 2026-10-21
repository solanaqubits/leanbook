# v0.7.35 — structural accounting for quota search

Adds CryptoHiddenScalarQuotaCostContract (epsilon231), registry integration,
compact regressions and English documentation. Private source:
`c754a6214ef2adb81084cde0fee234b3c7d0622f`. Inventory: 233 direct MasterSuite
imports and 277 byte-identical Lean sources including Verification.lean.

The instrumented transition materializes annotated entries and counts exactly
n active-entry updates. Removing annotations returns quotaNextRow for any row.
The scan accumulates checks, transitions and updates, preserving its result
against both streaming and reference selectors for every rational profile,
tolerance and cap, with no probability-range assumptions.

Success some T yields (T+1,T,n*T); exhaustion none yields (cap+1,cap,n*cap).
The explicit structural unit-cost bound is C <= 2*(n+1)*(cap+1), including
initialization and absorbing entries. No library IsBigO theorem, rational bit
complexity, profile-evaluation cost, compiled instruction count, allocation,
algorithm memory or machine-time bound is claimed. Prior benchmarks are separate.
26 IO scenarios run within the compound live test; 32 Lean examples include
registry checks. The explicit qutrit Spec build and old memory fix are preserved.

Independent public epsilon/scoped checks use strict Lake, every public unittest
with live mode, integration/catalog checks and a single transitive union axiom
audit. Allowed axioms: propext, Classical.choice, Quot.sound; no native_decide.
Local checks preserve the incremental cache under an 8 GiB memory cap, swap off.
Lake remains 0.7.1. Full public beta remains v0.7.1,
`2419489245019fb16e32ffac641b9f88eea94126`; no new full beta checkpoint is claimed.
Private coordination, research files, raw evidence and ancestry are excluded.
