---
id: QuantumNullConditioning
language: en
section: quantum-physics
source: Verification/QuantumNullConditioning.lean
source_sha256: e58a2a95e52db94d6d81ee5f3344df928f5ef59fdd6f8e96fd363d3ca76fc13b
novelty: not-assessed
status: reviewed
---

# QuantumNullConditioning

[Section](README.md) · [Lean source](../../Verification/QuantumNullConditioning.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Zero-probability branches, total conditional matrices and reconstruction.
Zero is a sentinel matrix for an impossible event, never a normalized quantum state.

A zero matrix is the sentinel for an impossible event and is not a normalized state. PSD plus zero trace forces the complete branch matrix to vanish. A confused classical report may still be delivered from another physically allowed branch.

## Checked declarations

- `psd_trace_real`
- `psd_zero_probability_iff`
- `micro_zero_iff`
- `outcome_zero_iff`
- `normalize_positive`
- `normalize_trace_one`
- `normalize_null`
- `normalize_reconstruct`
- `micro_reconstruct`
- `outcome_reconstruct`
- `impossible_outcome`
- `reported_barycenter`
- `positive_reported_barycenter`
- `accepted_reconstruct`
- `conditional_v411_refinement`
- `conditional_barycenter`
- `conditional_weights_total`
- `accepted_null_all_reports`
- `ghz_psi_micro_null`
- `ghz_ideal_report_null`
- `zero_true_branch_nonzero_report`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.
