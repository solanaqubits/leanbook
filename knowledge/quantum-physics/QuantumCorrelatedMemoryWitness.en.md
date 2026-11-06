---
id: QuantumCorrelatedMemoryWitness
language: en
section: quantum-physics
source: Verification/QuantumCorrelatedMemoryWitness.lean
source_sha256: 742bd9f7b05e3473eca811b764c6b333bcadeea6300def4fe561d431d2c3682f
novelty: not-assessed
status: reviewed
---

# QuantumCorrelatedMemoryWitness

[Section](README.md) · [Lean source](../../Verification/QuantumCorrelatedMemoryWitness.lean) ·
[Scope and verification](../../docs/quantum-v4.21.md)

A fixed environment-controlled X gate acts on B BEFORE the ideal Bell analyzer.
It is represented by an explicit involutive permutation on FourIndex × Fin 2.
The two PSD trace-one inputs have equal system marginals and equal environment
marginals, but give Phi+ and Psi+ corrected outputs. Every reported branch has
trace 1/4 for both inputs. The accepted target overlaps are exactly 1 and 0.
No function of the initial system marginal alone can reproduce every density
input for this fixed stage list and perfect readout, even if the function is
nonlinear. This is a concrete obstruction, not a general assignment-map theorem.

The placement of the controlled gate matters: memoryStages E F applies E AFTER
CNOT(B→C). This witness instead prepends an identity ideal gate followed by the
controlled interaction; the ideal analyzer hypothesis is preserved.

## Declarations

- `QuantumCorrelatedMemoryWitness.flipEB_involutive`
- `QuantumCorrelatedMemoryWitness.flipEB_eq_iff`
- `QuantumCorrelatedMemoryWitness.coupling_left`
- `QuantumCorrelatedMemoryWitness.coupling_right`
- `QuantumCorrelatedMemoryWitness.coupling_adjoint`
- `QuantumCorrelatedMemoryWitness.coupling_squared`
- `QuantumCorrelatedMemoryWitness.coupling_entry`
- `QuantumCorrelatedMemoryWitness.witness_ideal`
- `QuantumCorrelatedMemoryWitness.effective_identity_memory`
- `QuantumCorrelatedMemoryWitness.witness_effective`
- `QuantumCorrelatedMemoryWitness.input_positive`
- `QuantumCorrelatedMemoryWitness.input_trace`
- `QuantumCorrelatedMemoryWitness.coupling_prepared`
- `QuantumCorrelatedMemoryWitness.witnessPlus_posSemidef_and_trace_one`
- `QuantumCorrelatedMemoryWitness.witnessMinus_posSemidef_and_trace_one`
- `QuantumCorrelatedMemoryWitness.trace_environment_add`
- `QuantumCorrelatedMemoryWitness.witness_same_system_marginal`
- `QuantumCorrelatedMemoryWitness.trace_system_prepared`
- `QuantumCorrelatedMemoryWitness.witness_same_environment_marginal`
- `QuantumCorrelatedMemoryWitness.witness_reduced_plus`
- `QuantumCorrelatedMemoryWitness.witness_reduced_minus`
- `QuantumCorrelatedMemoryWitness.witness_branch_plus`
- `QuantumCorrelatedMemoryWitness.witness_branch_minus`
- `QuantumCorrelatedMemoryWitness.scaled_bell_distinct`
- `QuantumCorrelatedMemoryWitness.witness_same_branch_trace_but_diff_branch_matrix`
- `QuantumCorrelatedMemoryWitness.no_marginal_only_map_for_witness_config`
- `QuantumCorrelatedMemoryWitness.accepted_plus`
- `QuantumCorrelatedMemoryWitness.accepted_minus`
- `QuantumCorrelatedMemoryWitness.accepted_fidelity_gap`
- `QuantumCorrelatedMemoryWitness.witness_accepted_outputs_distinct`
- `QuantumCorrelatedMemoryWitness.verification_suite`

## Limits

Finite-dimensional single-cycle semantics; no adaptive process tensors, hardware
calibration, physical rate measurements, or universal novelty claim.
