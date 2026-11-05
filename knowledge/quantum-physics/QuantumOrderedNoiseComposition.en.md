---
id: QuantumOrderedNoiseComposition
language: en
section: quantum-physics
source: Verification/QuantumOrderedNoiseComposition.lean
source_sha256: a2424cad594e532a69300cf0d88e130413cbc5fc046a47d4465a26c7012eb1c1
novelty: not-assessed
status: reviewed
---

# QuantumOrderedNoiseComposition

[Section](README.md) · [Lean source](../../Verification/QuantumOrderedNoiseComposition.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Ordered finite noisy circuits. Every stage has its own finite Kraus index.
The direct path operator and the accumulated input-noise operator are defined
separately and related by a matrix factorization theorem.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `compose_map`
- `noisy_gate_map`
- `pullback_compose_map`
- `nested_pullback_map`
- `direct_map_run`
- `run_append`
- `path_factorization`
- `circuit_factorization`
- `run_effective`
- `run_trace`
- `run_positive`
- `singleton_effective`
- `two_stage_effective`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.
