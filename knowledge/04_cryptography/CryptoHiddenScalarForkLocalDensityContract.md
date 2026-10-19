---
id: CryptoHiddenScalarForkLocalDensityContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarForkLocalDensityContract.lean
novelty: not-assessed
status: reviewed
---

# Child laws and local full-probe density

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarForkLocalDensityContract.lean)

## Exact experiment

Fix one adversary model, tape, reachable parent snapshot and computed context.
A full probe is draw(u,v) with uniform microseeds in a finite product C times D.
The child schedule may depend on u; primitive seed blocks are independent.
Repeated preimages retain their weights. This is not uniform sampling of the
image, nor an arbitrary correlated joint law.

`product_event_average` and `full_probe_rate_eq_average` prove exact averaging:
full success probability is the average over C of the D-row success probabilities.
`full_probe_density_lower` gives d=average(C,delta) from row bounds delta(u).
`average_bounds` proves 0<=d<=1 when C is nonempty and each delta lies in [0,1].
`good_call_density_lower` gives alpha*delta from a good subset of call microseeds.
`full_probe_class_mass_eq` preserves the call-class mass when the key depends only
on u and D is nonempty. Different calls may have different success probabilities;
independence between success and class is not required.

## Exact snapshots and composition

`round_attempt_child_event` and `eta_attempt_child_event` identify full success
with the existing child acquireTree at Observation.after and the exact computed
child_statement or toIPA context. roundChildRate and etaChildRate explicitly
match the primitive query: abort contributes zero, success uses that child's
finite schedule law. `round_density_lower` and `eta_density_lower` average these
child bounds. They do not identify snapshots merely by equal algebraic statements.

outerChildRate checks the actual post-e packet and scalar equation; abort, wrong
packet and false equation contribute zero. `outer_child_rate_eq` reuses epsilon216's
node_collect_event to identify the quota2 child event. `outer_density_lower`
discharges the full acquireNode density premise from these child laws.

`averaged_collect_probability_lower` reuses epsilon217 for arbitrary coherent
quotas, with preserved beta. `averaged_acquisition_probability_lower` supplies the
actual outer quota3 bound. Existing positive_schedule_probability_extracts then
gives model provenance and the witness-or-relation conclusion; the regression
exercises this on six depth-one trees. No collector or extractor is replaced.

## Positivity and limits

`quota_positive` proves positivity with enough trials and positive rates at all
required states. `linear_quota_positive` specializes to n>0, T>=n, beta>=0,
d<=1 and d>(n-1)*beta. This is a sufficient condition for the conservative
reference bound, not a necessary condition for actual collector success.

Regressions have d=3/4, beta=1/2, quota2/T2: bound3/16 and actual probability1/4.
Using the valid but loose beta=1 gives bound0 despite positive actual success.
Other regressions preserve weighted calls, reject correlated suffix substitution,
and distinguish reachable snapshots with equal Statement but child densities1/0.
Abort, unexpected packets, invalid scalar equations, empty seed sets, depth-one
acquisition and the F11 nested zero-bound example are covered.

Child-law estimates remain explicit. No automatic recursive density certificate
for arbitrary adversaries, inference from global acceptance, general Bellare–Neven,
ROM/Fiat–Shamir, external-process refinement or polynomial-time bound is claimed.
The finite product construction may represent rational weighted calls through
microseed multiplicity; arbitrary real or dependent laws need a separate adapter.
The existing ResourceTrace and schedule bounds remain unchanged. Exact Q(k)/R(k)
formulas remain Clean-only; initial abort has Q=1,R=0. Full beta baselines remain
historical; the integration report records actual epsilon/scoped checks.
