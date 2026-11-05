---
id: QuantumLocalPostNoise
language: en
section: quantum-physics
source: Verification/QuantumLocalPostNoise.lean
source_sha256: 5b49c01fc8644dcc0f4d9e02447032b51985e5f6c642b83421e6a5815a8808ff
novelty: not-assessed
status: reviewed
---

# QuantumLocalPostNoise

[Section](README.md) · [Lean source](../../Verification/QuantumLocalPostNoise.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Local CPTP noise on D preserves the A marginal. Local and pair depolarization
are different maps; their agreement requires a maximally mixed A marginal.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `embedD_adjoint`
- `embedD_mul`
- `embedD_one`
- `embedD_sum`
- `onD_map`
- `onD_preserves_A`
- `pauli_error_physical`
- `qubit_depolarizing_map`
- `local_depolarizing_entry`
- `local_depolarizing_formula`
- `local_depolarizing_preserves_A`
- `local_equals_pair_of_marginal`
- `local_equals_pair_iff`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.
