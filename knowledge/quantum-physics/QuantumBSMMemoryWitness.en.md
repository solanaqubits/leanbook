---
id: QuantumBSMMemoryWitness
language: en
section: quantum-physics
source: Verification/QuantumBSMMemoryWitness.lean
source_sha256: a6da1ff07645fd22ffc555928722986390d7762fe94dcf70dfd47140256a9a64
novelty: not-assessed
status: reviewed
---

# QuantumBSMMemoryWitness

[Section](README.md) · [Lean source](../../Verification/QuantumBSMMemoryWitness.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

An explicit spectator-to-environment CNOT echo inside the Bell analyzer.
Retained and reset environments have identical Bell-message probabilities but
different corrected outer-pair density matrices on two perfect input Bell pairs.

The concrete input consists of two ideal Bell pairs and a pure binary environment. Two spectator-controlled collisions cancel if the environment is retained. Resetting between stages produces a different output: all four Bell report probabilities remain one quarter, but target fidelity changes from one to one half and the outer-pair coherence vanishes. This is a finite mathematical witness, not a measured hardware error model.

## Checked declarations

- `central_preserves_flag`
- `effective_echo`
- `retained_outcome`
- `computational_branch_analysis`
- `readout_after_analysis`
- `reset_evolution`
- `reset_outcome`
- `input_valid`
- `dephased_input`
- `perfect_report_matrix`
- `perfect_report_product`
- `retained_branch`
- `reset_branch`
- `mixed_outer_valid`
- `same_report_probabilities`
- `retained_output`
- `reset_output`
- `outputs_normalized`
- `outputs_positive`
- `rejection_absent`
- `output_fidelity_gap`
- `output_coherence_gap`
- `outputs_distinct`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.
