# v0.7.28 — decidable quota margin certificates

This scoped release adds CryptoHiddenScalarQuotaMarginContract (epsilon224),
its registry integration, kernel/runtime regressions and English documentation.
It synchronizes 226 direct MasterSuite imports and 270 byte-identical formal Lean
sources with pinned source 577db4ed65eafe779dc94a3b43f89c08aaf4f694.

The recursive arithmetic certificate checks child certificates, sufficient budgets
and strict margins (n−1)beta < heavyMass(parent cutoff, child cutoff)*childBound.
The existing quota positivity theorem is reused at quotas 4/2/3; depth zero
introduces no artificial quota four. The certificate is executable.

finiteRootLower returns zero for an empty set and the exact minimum of computed
root bounds otherwise. Certified nonempty sets have a positive minimum. Tape
weights and acceptance are separate: extraction requires a qualifying subset G
with positive original mass W(G). The global adapter additionally requires root
cutoffs at most theta<1, weighted acceptance at least alpha>theta and certificates
on qualifying tapes. No external positive quota constant is postulated.

The resulting lower bound applies to the existing acquisition algorithm and
witness-or-generator-relation extractor. Original finite ProtocolPlan microseeds,
dependent seed spaces and snapshot decoders remain unchanged. No new collector,
conditional resampling, ROM result, polynomial search guarantee or hardware test
is introduced. A positive arithmetic certificate does not imply acceptance;
a zero conservative bound does not prove impossible actual success.

Regression coverage includes actual F5 depth-zero and F37 depth-one plans with
proved class masses, heterogeneous budgets, empty and zero-mass tape sets,
insufficient budgets, exact zero margins, flat cutoffs and initial aborts.
The F5 model executes the collector and extracts the zero witness. Its positive
root bound is 8711401623057/125000000000000. The 23 new runtime scenarios execute
inside the live unittest suite and must not be added to its test count.

Verification scope: independent public scoped Lake --wfail, live unittest,
registry/catalog checks and one transitive union axiom audit. Publication is
conditional on all checks passing; exact observed metrics are recorded in the
annotated tag and release commit. Allowed axioms are propext, Classical.choice
and Quot.sound; no native-decide shortcut. Private proof reports do not certify
this public checkout.

Lake remains 0.7.1. The historical full public beta basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); no new full beta run is claimed.
Private knowledge cards, raw logs and SimLab materials are excluded from export.
