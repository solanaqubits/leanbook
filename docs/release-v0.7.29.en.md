# v0.7.29 — explicit factorized quota bounds

This scoped release adds CryptoHiddenScalarQuotaProductContract (epsilon225),
registry integration, kernel/runtime regressions and English documentation.
It synchronizes 227 direct MasterSuite imports and 271 byte-identical formal Lean
sources with pinned source 4a53e69c27b2d9aacb64356ba373246b92a5282c.

The existing quotaLower recursion has an exact diagonal identity at budget n-j:
Q(n-j,j) = product of p_i over j <= i < n. This identity is algebraic and needs
no probability ranges. The insufficient-budget result is reused from epsilon216
through an explicit signature adapter. Budget monotonicity and product lower
bounds require 0 <= p_i <= 1 for i < n. Growth can be strict or stationary.

linearQuotaProduct is the product of max(0,d-j*beta). Under 0 <= d <= 1,
beta >= 0 and sufficient budget T >= n it bounds quota(n,T,d,beta) from below.
A strict margin removes max; 0 < mu <= d-(n-1)*beta gives the explicit chain
0 < mu^n <= linearQuotaProduct <= quota.

Node adapters retain the exact existing child threshold bound. No new bottom-up
recursion replacing child bounds by products is introduced. protocolProductLower
is a pure three-factor diagonal, independent of root budget. finiteProductLower
is its exact minimum on a nonempty tape set, and zero on the empty set.
Its comparison with finiteRootLower requires root budget >= 3 on every tape in G.
The budget-two regression has positive product but zero root quota, also refuting
an unqualified singleton minimum comparison.

The success-probability bound additionally requires G to be a qualifying subset.
Certificates from epsilon224 and positive original tape mass W(G) give strict
positivity and the existing witness-or-generator-relation extraction result.
Certificates already supply the required root budget. Original finite per-tape
ProtocolPlan microseeds, dependent seed spaces and snapshot decoders are retained.
A zero conservative bound does not imply actual impossibility.

Regressions cover real F5 depth-zero and F37 depth-one plans, empty/absorbed states,
insufficient budgets, strict and stationary growth, zero margins, mu^n,
heterogeneous tape budgets, empty and zero-mass tape sets, and actual acquisition
and extraction of the zero witness in the F5 model. For n=4,d=1,beta=1/8 the product
is 105/256; mu=5/8 gives 625/4096. The budget-two counterexample has product
8711401623057/125000000000000 and quota zero. A profile p=2 also demonstrates that
budget monotonicity can fail without range assumptions. The 28 IO scenarios run
within live unittest and are not added to its test count.

Independent public scoped checks include Lake --wfail, live unittest, registry
and catalog checks, and one transitive union axiom audit. Publication requires all
checks to pass; actual metrics are recorded in the release commit and annotated
tag. Allowed axioms: propext, Classical.choice, Quot.sound; no native_decide.
Private reports do not certify the public checkout.

Lake remains 0.7.1. The full public beta basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); no new full beta is claimed.
No new collector/extractor, conditional resampling, ROM, polynomial-time or hardware
claim is introduced. Private coordination, raw logs and SimLab materials are excluded.
