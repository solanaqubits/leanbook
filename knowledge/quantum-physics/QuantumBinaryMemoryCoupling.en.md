---
id: QuantumBinaryMemoryCoupling
language: en
section: quantum-physics
source: Verification/QuantumBinaryMemoryCoupling.lean
source_sha256: 585206685ad431c93d23537e07fa13b7cb29d14d348eead3f52cdf06b09b8e4b
novelty: not-assessed
status: reviewed
---

# QuantumBinaryMemoryCoupling

[Section](README.md) · [Lean source](../../Verification/QuantumBinaryMemoryCoupling.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

A binary environment controlled by a system basis label. Two coherent
couplings cancel, whereas discarding the environment removes inter-label coherence.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `flip_involutive`
- `flip_eq_iff`
- `coupling_left`
- `coupling_right`
- `coupling_adjoint`
- `coupling_squared`
- `coupling_map_entry`
- `reduced_coupling`
- `dephase_idempotent`
- `coupling_commutes`
- `coupling_twice`
- `extend_prepare`
- `commuting_sandwich`
- `dephase_sandwich`
- `reduced_noisy_coupling`
- `pullback_coupling`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.
