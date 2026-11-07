---
id: QuantumNoisyRepeaterWitness
language: en
section: quantum-physics
source: Verification/QuantumNoisyRepeaterWitness.lean
source_sha256: a278ba9f41e027d30a31c58534abb71b75d0eca2367c2a9daf94ff76793d7625
novelty: not-assessed
status: reviewed
---

# QuantumNoisyRepeaterWitness

[Section](README.md) · [Scope](../../docs/quantum-v4.39.md) ·
[Source](../../Verification/QuantumNoisyRepeaterWitness.lean)

For fixed post-depolarization quality 19/20 and initial Visibility 4/5, the
chronological noisy schedule 16 then 16 has strict gain on each spatial level.
The channel and operator composition are those of QuantumScheduledNoisyRepeater:
ideal swapping, independent resource copies and noise on every retained BBPSSW
output pair. No asymmetric input memory model is introduced.

Two 16-step rational interval chains are checked by the Lean kernel. The generic
interval-step proof uses monotonicity on [1/4,1] and exact endpoint inequalities.
The second chain starts from an enclosure of the actual first output. The first
visibility lies in [0.8022568,0.8022572], the second in [0.8029727,0.8029731].
All endpoints are exact terminating rationals, not floating-point hypotheses.

Both swapped inputs are inside the working window. Thus each purification orbit
is strictly increasing, and a bound at depth 15 excludes every smaller depth.
The first minimum is relative to the original 4/5; the second is relative to the
output after first depth 16. Neither is a global schedule-optimality claim.

The two strict gains imply LocalQualityGain and strict improvement for both
nonempty prefixes. Existing accumulator refinement yields the unnormalized
matrix, PSD, positive weight at most one, trace and conditional normalization.
The resource theorem gives four segments and 2^34=17179869184 raw pairs. It does
not estimate expected resources under retries or prove a nonzero yield.

Source certificate generation is not trusted: each rational transition is proved
by norm_num, with no native_decide or raised proof limits. Counts are code metrics;
novelty and scientific priority have not been assessed.

## Theorems

- [`QuantumNoisyRepeaterWitness.noisyRecurrence_mono_of_ge_quarter`](../../Verification/QuantumNoisyRepeaterWitness.lean#L27)
- [`QuantumNoisyRepeaterWitness.noisyOrbit_interval_step`](../../Verification/QuantumNoisyRepeaterWitness.lean#L35)
- [`QuantumNoisyRepeaterWitness.first_orbit_certificate`](../../Verification/QuantumNoisyRepeaterWitness.lean#L46)
- [`QuantumNoisyRepeaterWitness.second_orbit_certificate`](../../Verification/QuantumNoisyRepeaterWitness.lean#L120)
- [`QuantumNoisyRepeaterWitness.initial_swap_fidelity`](../../Verification/QuantumNoisyRepeaterWitness.lean#L195)
- [`QuantumNoisyRepeaterWitness.first_level_value`](../../Verification/QuantumNoisyRepeaterWitness.lean#L198)
- [`QuantumNoisyRepeaterWitness.second_level_value`](../../Verification/QuantumNoisyRepeaterWitness.lean#L206)
- [`QuantumNoisyRepeaterWitness.first_level_visibility_bounds`](../../Verification/QuantumNoisyRepeaterWitness.lean#L210)
- [`QuantumNoisyRepeaterWitness.second_swap_fidelity_bounds`](../../Verification/QuantumNoisyRepeaterWitness.lean#L219)
- [`QuantumNoisyRepeaterWitness.second_level_visibility_bounds`](../../Verification/QuantumNoisyRepeaterWitness.lean#L226)
- [`QuantumNoisyRepeaterWitness.first_level_depth_15_lt_initial`](../../Verification/QuantumNoisyRepeaterWitness.lean#L235)
- [`QuantumNoisyRepeaterWitness.first_level_depth_16_gt_initial`](../../Verification/QuantumNoisyRepeaterWitness.lean#L240)
- [`QuantumNoisyRepeaterWitness.second_level_depth_15_lt_initial`](../../Verification/QuantumNoisyRepeaterWitness.lean#L243)
- [`QuantumNoisyRepeaterWitness.second_level_depth_15_lt_first`](../../Verification/QuantumNoisyRepeaterWitness.lean#L248)
- [`QuantumNoisyRepeaterWitness.second_level_depth_16_gt_first`](../../Verification/QuantumNoisyRepeaterWitness.lean#L253)
- [`QuantumNoisyRepeaterWitness.witness_swap_inside_window`](../../Verification/QuantumNoisyRepeaterWitness.lean#L257)
- [`QuantumNoisyRepeaterWitness.first_level_minimal_depth_16`](../../Verification/QuantumNoisyRepeaterWitness.lean#L273)
- [`QuantumNoisyRepeaterWitness.second_level_minimal_depth_16`](../../Verification/QuantumNoisyRepeaterWitness.lean#L282)
- [`QuantumNoisyRepeaterWitness.witnessSchedule_localQualityGain`](../../Verification/QuantumNoisyRepeaterWitness.lean#L293)
- [`QuantumNoisyRepeaterWitness.witnessSchedule_sustains_initial_quality`](../../Verification/QuantumNoisyRepeaterWitness.lean#L310)
- [`QuantumNoisyRepeaterWitness.witnessSchedule_refinement_and_psd`](../../Verification/QuantumNoisyRepeaterWitness.lean#L316)
- [`QuantumNoisyRepeaterWitness.witnessSchedule_trace`](../../Verification/QuantumNoisyRepeaterWitness.lean#L326)
- [`QuantumNoisyRepeaterWitness.witnessSchedule_conditional`](../../Verification/QuantumNoisyRepeaterWitness.lean#L331)
- [`QuantumNoisyRepeaterWitness.witnessSchedule_conditional_density`](../../Verification/QuantumNoisyRepeaterWitness.lean#L336)
- [`QuantumNoisyRepeaterWitness.witnessSchedule_resource_count`](../../Verification/QuantumNoisyRepeaterWitness.lean#L340)
- [`QuantumNoisyRepeaterWitness.verification_suite`](../../Verification/QuantumNoisyRepeaterWitness.lean#L355)
