---
id: QuantumDecoupledEnvironment
language: en
section: quantum-physics
source: Verification/QuantumDecoupledEnvironment.lean
source_sha256: e464a043a8cf82f65077b2458438e652aed46d29510d1a9306c11e7e974bde73
novelty: not-assessed
status: reviewed
---

# QuantumDecoupledEnvironment

[Section](README.md) · [Lean source](../../Verification/QuantumDecoupledEnvironment.lean) ·
[Scope](../../docs/quantum-v4.22.md)

Extends system stages by an untouched finite environment. For every joint matrix,
all five reduced outcomes equal the system instrument on the initial marginal.
No PSD, factorization or ideal-analyzer premise is needed for this algebraic equality.
A separate tensor-CPTP theorem eliminates arbitrary independent trace-preserving
environment noise, without requiring unitality. The proof uses environment block
traces and the Kraus completeness conditions. Chronological run lemmas avoid
identifying dependent path-label types by assumption.

These are sufficient conditions, not a characterization of all reducible interactions.
Correlations can persist in the full joint state. The perfect-readout reject branch
alone would be vacuous; the proved outcome theorem covers arbitrary Readout.

## Declarations

- `QuantumDecoupledEnvironment.extend_sum`
- `QuantumDecoupledEnvironment.traceEnvironment_extendCPTP`
- `QuantumDecoupledEnvironment.traceEnvironment_extendStages_run`
- `QuantumDecoupledEnvironment.reduced_micro_run`
- `QuantumDecoupledEnvironment.reduced_reject_run`
- `QuantumDecoupledEnvironment.system_micro_run`
- `QuantumDecoupledEnvironment.system_reject_run`
- `QuantumDecoupledEnvironment.extendStages_outcome_depends_only_on_system_marginal`
- `QuantumDecoupledEnvironment.extendStages_same_system_marginal_eq_output`
- `QuantumDecoupledEnvironment.traceEnvironment_environment_channel`
- `QuantumDecoupledEnvironment.traceEnvironment_tensorCPTP`
- `QuantumDecoupledEnvironment.verification_suite`

## Limits

Finite-dimensional one-cycle semantics. No adaptive process tensors, general
assignment-map classification, hardware characterization, or novelty claim.
