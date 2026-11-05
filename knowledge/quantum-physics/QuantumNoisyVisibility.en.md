---
id: QuantumNoisyVisibility
language: en
section: quantum-physics
source: Verification/QuantumNoisyVisibility.lean
source_sha256: 678c8867fb45550a1dae3d5b423bcd8bd3fc7bc315bf7911509e035466dc7602
novelty: not-assessed
status: reviewed
---

# QuantumNoisyVisibility

[Section](README.md) · [Lean source](../../Verification/QuantumNoisyVisibility.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Visibility multiplication for explicitly specified channels: central BC
isotropic depolarization, perfect readout, and output AD isotropic depolarization.
No universal fidelity-degradation claim is made for arbitrary CPTP maps.

The visibility product is derived only for the specified central-pair isotropic pre-noise, ideal classical readout and isotropic output noise. An explicit CPTP counterexample rejects the claim that all physical channels must decrease target fidelity.

## Checked declarations

- `uniform_density`
- `fully_mixed_input`
- `ideal_accepted`
- `fully_mixed_output`
- `isotropic_mix`
- `isotropic_trace`
- `depolarizing_isotropic`
- `common_post_aggregate`
- `noisy_visibility_matrix`
- `noisy_visibility_fidelity`
- `noisy_visibility_trace`
- `isotropic_fidelity_nonincreasing`
- `cptp_can_increase_target_fidelity`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.
