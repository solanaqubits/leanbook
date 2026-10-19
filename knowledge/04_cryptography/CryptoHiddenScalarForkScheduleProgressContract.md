---
id: CryptoHiddenScalarForkScheduleProgressContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarForkScheduleProgressContract.lean
novelty: not-assessed
status: reviewed
---

# Independent full-probe schedules and retained-branch progress

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarForkScheduleProgressContract.lean)

## Concrete law and assumptions

Fix a nonempty finite microseed set C, a deterministic draw function and the actual
snapshot collector's Attempt. Each microseed determines a full probe, including its
entire child schedule. `iidSchedule` maps the existing product space `productTapes C T`
to a candidate list; uniform sampling of this space means independent sampling
with replacement. Multiple microseeds may map to the same candidate. Their weights
are preserved; replacing this experiment with uniform sampling of the image is invalid.

`KeyCoherent` is inherited from epsilon216: every successful value has the candidate's
key. With one fixed parent snapshot, d is a lower bound on full-probe success,
beta is an upper bound on each key class's mass, and j is the number of retained
successful distinct keys. The rates are

    p(j) = max(0, d - j * beta),   0 <= d <= 1, beta >= 0.

Beta is neither a depth penalty nor a budget penalty. Full child-acquisition success
is included in d. Independence between success and key is NOT assumed. Density at
one snapshot cannot be transferred to another merely because their algebraic
statements coincide. A global acceptance probability does not imply these densities.

## Proof bridge

`resample_sum` proves an exact finite-product identity by the involution
(w,u) -> (update w i u, w i). `fresh_event_count` shows that a fresh coordinate
retains its uniform law on any event unchanged by resampling it, including a fixed
strict prefix. The formula uses cardinalities, so empty conditioning events cause
no division by zero. `schedule_prefix_update` proves this independence for the
actual collector prefix, rather than postulating that the scan is Markov.

`blocked_mass_le` sums the fiber masses of the j retained classes. The exact
`scan_step_progress` equivalence identifies an increment with success outside those
classes. The existing epsilon216 `unblocked_probability_lower` gives max(0,d-j beta).
`resampling_progress` aggregates the history bounds into the count-conditioned
cardinality inequality. `iid_progress_bounds` therefore derives ProgressBounds;
it does not take ProgressBounds as an assumption.

`iid_collect_probability_lower` composes with the existing quotaLower theorem.
`iid_tree_probability_lower`, `iid_node_probability_lower` and
`iid_acquisition_probability_lower` use the existing 4/2/3-level event adapters and
actual observations. `iid_positive_extracts` supplies an actual sampled schedule,
ForkProvenance and witness-or-relation extraction. There is no new collector,
retry recurrence or algebraic extractor. `class_mass_of_card_le` translates a
counted fiber cap into its probability cap.

## Regression and resource scope

Regressions distinguish iid replacement (two successes among four seeds, quota2,
budget2: 1/8) from sampling without replacement (1/6). They check conditional
freshness, early exit, failed-key retry, duplicate rejection, correlated-repeat
failure of an unjustified bound, and nonuniform pushforward masses 3/4 versus 1/2.
F11 square classes give beta=1/5 and quota4/budget4 bound24/125; F7 has only three
nonzero square classes and cannot fill quota4. A depth-one F11 snapshot model
composes the new theorem with six four-leaf trees and actual extraction.

T counts local scheduled probes, not physical runtime. Existing ResourceTrace
costs and schedule upper bounds are unchanged. Q(k)=4+2(4^(k+1)-1), R(k)=Q(k)-1
remain exact only for Clean successful traversals; initial abort has Q=1,R=0.
Independent child blocks permit retries after failure; reusing the same suffix is
not justified by the iid theorem. Without-replacement laws are compared in tests,
not covered by this universal iid adapter. Arbitrary real probability laws, global
acceptance-to-density, general Bellare–Neven, ROM/Fiat–Shamir, external-process
refinement and polynomial time are not established. Full beta baselines are preserved.
