# v0.7.23 — recursive hidden-scalar fork quota bounds

This scoped release exports epsilon218 and epsilon219: exact child-law averaging
and bottom-up recursive quota bounds for actual snapshot acquisition.

The public tree has219 direct MasterSuite imports and263 Lean sources identical
to private source7a981e35918c60b9d0ad3e7be4d843d9ed8fcf96.
Lake package version remains0.7.1. The full public beta baseline remains
2419489245019fb16e32ffac641b9f88eea94126; this is not a new full beta run.

## Contracts

CryptoHiddenScalarForkLocalDensityContract derives full-probe density by averaging
child success bounds under exact finite product laws, retaining microseed weights
and key-class masses. Its sufficient positivity threshold does not assert that
a zero conservative bound means zero actual success.

CryptoHiddenScalarForkRecursiveQuotaContract derives those child bounds recursively
from actual leaf checks. TreePlan.probability_lower bounds acquireTree;
EtaPlan.probability_lower handles quota2; ProtocolPlan.probability_lower handles
quota3 and acquireCompressedFork. ProtocolPlan.positive_extracts composes with
existing model provenance and witness-or-relation extraction.

Concrete laws use finite independent microseeds, common shape/budget by depth,
and call decoders indexed by exact snapshots. Arbitrary variable-cardinality or
real-weight laws require a separate adapter. No success estimate for internal
subtrees is assumed. No new collector or extractor is introduced.

## Regressions and boundaries

The F37 positive example uses8 distinct square classes,4 eta calls and32 e calls.
Exact class masses1/8,1/4,1/32 and budgets4/2/3 give:
105/256 →4305/65536 →2030724465/281474976710656 >0.
The corrected numerator equals4305*2257*209. Trusted-kernel finite decisions are
used, without native_decide. Actual schedules succeed at depths0,1,2. Other cases
cover exact probability6/125 with zero conservative bound, distinct reachable
snapshots with equal contexts, biased schedules, malformed packets, initial abort,
and actual extraction.

ResourceTrace describes the existing collector, not all pure decoder evaluation.
Exact Q(k),R(k)=Q(k)-1 formulas apply only to Clean successful runs. Arbitrary
runs retain their logs and schedule-size bounds; initial abort hasQ1,R0.
No inference from global adversary acceptance, general Bellare–Neven theorem,
external-process refinement, Fiat–Shamir/ROM, hardness or polynomial-time result
is asserted. Hardware deployment is outside this release.

Independent public scoped verification covers Lake --wfail, selected live unittest,
and one union transitive axiom audit through AxiomAudit; publication records exact
counts and source fingerprints. Allowed axioms are propext,Classical.choice,Quot.sound.
Private research material and repository ancestry are excluded from this export.
