# v0.7.38 — certified resumable quota search

Adds CryptoHiddenScalarQuotaResumableContract (epsilon234), registry integration,
compact regressions and English documentation. Pinned private source:
`fc1a3aeed7e1e66df30d93e67bfa32f5f8e21d8d`. Inventory: 236 direct MasterSuite
imports and 280 byte-identical Lean sources including Verification.lean.

QuotaSearchCursor retains the actual materialized vector row, its equality with
quotaRow at the historical bound, and a certificate that every budget through
that bound failed. Parameters n,p,j,epsilon remain fixed. A found constructor
alone is not a minimality proof: IsMinimalQuotaBudget specifies that separately.

initQuotaSearch checks budget zero; startQuotaSearch scans the inclusive window.
An exhausted cursor at a covered cap is returned unchanged; otherwise continuation
advances one row and scans only the new suffix. Exhausted continuation equals
cold reference search for every new cap. On exhaustion the retained bound is
the maximum of the old bound and the requested cap.

A genuinely minimal found T is preserved and matches cold reference search iff
T <= newCap. End-to-end and repeated continuation require nondecreasing caps.
All rational profiles and tolerances are supported, without probability ranges.
32 IO scenarios run inside the compound live test; 40 Lean examples include
registry checks. Regressions cover retained rows, calibrations4/6, shrinking
exhausted windows and the counterexample to shrinking after success.
No continuation cost counters, serialization, external cursor authentication,
physical timing or memory bound is claimed. Minimality concerns quotaLower,
not the actual physical success probability of the collector.

Independent public epsilon/scoped validation uses strict Lake, all public
unittests with live mode, integration/catalog checks and a single transitive
union axiom audit. Allowed axioms: propext, Classical.choice, Quot.sound;
no native_decide. Explicit qutrit Spec building and the old memory fix remain.
Local checks preserve the incremental cache under an 8 GiB memory cap with
swap off. Lake remains 0.7.1. The full public beta remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1); no new full beta checkpoint.
Private coordination, research files, raw evidence and ancestry are excluded.
