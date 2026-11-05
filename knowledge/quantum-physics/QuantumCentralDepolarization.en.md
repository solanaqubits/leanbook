---
id: QuantumCentralDepolarization
language: en
section: quantum-physics
source: Verification/QuantumCentralDepolarization.lean
source_sha256: da66027a582650cadb966878ce94d0ef897684adf280af38cd6946fdfa5967b7
novelty: not-assessed
status: reviewed
---

# QuantumCentralDepolarization

[Section](README.md) · [Lean source](../../Verification/QuantumCentralDepolarization.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Real-visibility depolarization and a local lift to the central pair BC.
The pre channel acts before the ideal Bell contraction, not at an unspecified gate location.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `probability_bounds`
- `sqrt_sandwich`
- `kraus_exact`
- `kraus_none_norm`
- `kraus_some_norm`
- `kraus_completeness`
- `linearChannel_trace`
- `linearChannel_add`
- `linearChannel_smul`
- `depolarizing_map`
- `depolarizing_covariance`
- `embedBC_adjoint`
- `embedBC_mul`
- `embedBC_one`
- `embedBC_sum`
- `central_map`
- `central_depolarizing_entry`
- `bell_left_marginal`
- `bell_right_marginal`
- `traceBC_product`
- `traceBC_sum`
- `traceBC_real_smul`
- `traceBC_input`
- `central_input_depolarization`
- `flip_ghz_density`
- `pre_flip_opens_ghz_branch`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.
