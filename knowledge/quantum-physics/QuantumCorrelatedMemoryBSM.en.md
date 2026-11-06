---
id: QuantumCorrelatedMemoryBSM
language: en
section: quantum-physics
source: Verification/QuantumCorrelatedMemoryBSM.lean
source_sha256: 04819b96e84b0a251cf3e982d233aeb4598f5da21ef1bb4c84d564db7caa0136
novelty: not-assessed
status: reviewed
---

# QuantumCorrelatedMemoryBSM

[Section](README.md) · [Lean source](../../Verification/QuantumCorrelatedMemoryBSM.lean) ·
[Scope and verification](../../docs/quantum-v4.21.md)

Final partial trace of the existing joint Bell instrument on an arbitrary joint matrix.
The input need not factor into a system density and a fixed environment density.
Rectangular operator sums with final environment selectors preserve positivity on
all finite ancillas. The map is linear. Zero trace of a PSD output is equivalent
to a zero branch. Under the explicit ideal-analyzer hypothesis, the five-outcome
trace equals the input trace. Existing v4.20 product bridges are reused, and finite
linear combinations of products are handled without imposing physical mixture
conditions on arbitrary complex coefficients.

The effective-channel bridge retains the FULL joint input until after evolution;
it does not define a channel solely on the initial system marginal.

## Declarations

- `QuantumCorrelatedMemoryBSM.weightedFamily_positive`
- `QuantumCorrelatedMemoryBSM.lift_weightedFamily`
- `QuantumCorrelatedMemoryBSM.weightedFamily_cp`
- `QuantumCorrelatedMemoryBSM.weightedFamily_add`
- `QuantumCorrelatedMemoryBSM.weightedFamily_smul`
- `QuantumCorrelatedMemoryBSM.reduced_outcome_some`
- `QuantumCorrelatedMemoryBSM.joint_family_partial_trace`
- `QuantumCorrelatedMemoryBSM.reducedJointMicro_kraus`
- `QuantumCorrelatedMemoryBSM.reducedJointReject_kraus`
- `QuantumCorrelatedMemoryBSM.outcome_weight_nonnegative`
- `QuantumCorrelatedMemoryBSM.reducedJointOutcome_family`
- `QuantumCorrelatedMemoryBSM.reducedJointOutcome_cp`
- `QuantumCorrelatedMemoryBSM.reducedJointOutcome_positive`
- `QuantumCorrelatedMemoryBSM.reducedJointOutcome_zero_iff`
- `QuantumCorrelatedMemoryBSM.reducedJointOutcome_product`
- `QuantumCorrelatedMemoryBSM.reducedJointOutcome_sum_products`
- `QuantumCorrelatedMemoryBSM.joint_reduction_effective`
- `QuantumCorrelatedMemoryBSM.joint_branch_effective`
- `QuantumCorrelatedMemoryBSM.reducedJointMicro_effective`
- `QuantumCorrelatedMemoryBSM.reducedJointReject_effective`
- `QuantumCorrelatedMemoryBSM.reducedJointOutcome_effective`
- `QuantumCorrelatedMemoryBSM.reducedJointOutcome_total_trace`
- `QuantumCorrelatedMemoryBSM.verification_suite`

## Limits

Finite-dimensional single-cycle semantics; no adaptive process tensors, hardware
calibration, physical rate measurements, or universal novelty claim.
