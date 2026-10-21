# v0.7.37 — fast boundary branches for quota search

Adds CryptoHiddenScalarQuotaFastContract (epsilon233), registry integration,
compact regressions and English documentation. Pinned private source:
`e145357b79f93440203d590dfdc3a2d81defee51`. Inventory: 235 direct MasterSuite
imports and 279 byte-identical Lean sources including Verification.lean.

The fast selector equals chooseQuotaBudgetWithin for all rational profiles,
tolerances and caps, without probability restrictions. Absorbed states return
some 0 exactly when tolerance is nonnegative. A zero search cap in an active
state returns some 0 exactly when tolerance is at least 1. Other inputs use
the existing streaming search.

Fast-branch structural counters are exactly one deficit check and zero row
initializations, transitions and active updates. Regular-branch counters equal
the instrumented streaming model. Natural-number control guards are excluded
from deficit-check counts. Zero row constructions does not assert zero machine
allocations, faster execution or a memory/bit-complexity bound.

Negative tolerance is not globally rejected: arbitrary rational profiles can
produce negative deficits. Successful selections are stable under larger search
caps without probability assumptions; none excludes solutions only inside the
supplied finite window. No deficit monotonicity outside probability ranges is
claimed. 26 IO scenarios run within the compound live test; 32 Lean examples
include registry checks. Explicit qutrit Spec building and the old memory fix
are preserved.

Independent public epsilon/scoped validation uses strict Lake, all public
unittests with live mode, integration/catalog checks and a single transitive
union axiom audit. Allowed axioms: propext, Classical.choice, Quot.sound;
no native_decide. Local checks preserve the incremental cache under an 8 GiB
memory cap with swap off. Lake remains 0.7.1. The full public beta remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1); no new full beta checkpoint.
Private coordination, research files, raw evidence and ancestry are excluded.
