---
id: QuantumMixedEnvironment
language: en
section: quantum-physics
source: Verification/QuantumMixedEnvironment.lean
source_sha256: 873e7c0d171b7ab9326512391ff3cffc9ef3e5c927e8df64e2796891acaacfa5
novelty: not-assessed
status: reviewed
---

# QuantumMixedEnvironment

[Section](README.md) · [Lean source](../../Verification/QuantumMixedEnvironment.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

A fixed arbitrary finite density matrix for an initially independent environment.
A square-root factor supplies Kraus preparation; its operational semantics depends
only on the density matrix, not on a chosen ensemble.

EnvironmentState carries an arbitrary finite PSD matrix of trace one. A canonical matrix square root supplies preparation Kraus operators even for singular states. Their sum is exactly tensoring with the environment density. The reduced CPTP map equals the final partial trace of the joint evolution. Ensemble semantics requires an explicit density decomposition equality; physical ensemble weights must additionally be nonnegative and normalized. Initial system-environment independence is essential.

## Checked declarations

- `factor_product`
- `prepare_op_sandwich`
- `preparation_semantics`
- `preparation_complete`
- `trace_tensor_state`
- `mixed_branch_partial_trace`
- `mixed_reduced_map`
- `density_extensionality`
- `ensemble_semantics`
- `mixed_identity`
- `pure_basis_limit`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.
