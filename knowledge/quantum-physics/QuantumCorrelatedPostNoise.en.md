---
id: QuantumCorrelatedPostNoise
language: en
section: quantum-physics
source: Verification/QuantumCorrelatedPostNoise.lean
source_sha256: 7ad4c90bcb7eab4f31cf49ea918f5ba99bceb034e0b51fe8718262faa5ba8b51
novelty: not-assessed
status: reviewed
---

# QuantumCorrelatedPostNoise

[Section](README.md) · [Lean source](../../Verification/QuantumCorrelatedPostNoise.lean) ·
[Scope and verification](../../docs/quantum-v4.24.md)

Applies a message-dependent CPTP channel on AD after the correlated-input joint
instrument. The input is the full system/environment matrix; no initial product
assumption is needed. Rejection is unchanged. Post-processing has no further
coupling to the retained environment.

Explicit Kraus operators have size 4 by (16 times environment dimension), with
path, environment-selector and post-channel labels. The weighted representation
and its square-root Kraus representation agree. Complete positivity includes
arbitrary finite ancillas. The map is complex-linear and preserves PSD.

Post noise preserves each microscopic and observed branch trace. For PSD inputs,
a zero branch remains zero and a nonzero branch cannot become zero. Five-outcome
trace balance reuses the explicit ideal-analyzer hypothesis of the earlier joint
instrument. Linear combinations of product inputs refine v4.20; the effective
4-by-16 noisy-instrument bridge requires a fixed initially independent environment.

Independent AD post-processing commutes with final environment trace. It also
preserves the v4.23 post-analyzer B-to-E invariance and tensor-stage reduction.
No injectivity of output matrices or monotonic fidelity degradation is claimed.

## Theorems

- [`QuantumCorrelatedPostNoise.post_weighted_family`](../../Verification/QuantumCorrelatedPostNoise.lean#L26)
- [`QuantumCorrelatedPostNoise.post_weighted_cp`](../../Verification/QuantumCorrelatedPostNoise.lean#L36)
- [`QuantumCorrelatedPostNoise.sqrt_sandwich_rectangular`](../../Verification/QuantumCorrelatedPostNoise.lean#L47)
- [`QuantumCorrelatedPostNoise.noisy_micro_weighted`](../../Verification/QuantumCorrelatedPostNoise.lean#L89)
- [`QuantumCorrelatedPostNoise.noisy_micro_kraus`](../../Verification/QuantumCorrelatedPostNoise.lean#L101)
- [`QuantumCorrelatedPostNoise.noisy_micro_cp`](../../Verification/QuantumCorrelatedPostNoise.lean#L111)
- [`QuantumCorrelatedPostNoise.noisy_micro_trace`](../../Verification/QuantumCorrelatedPostNoise.lean#L118)
- [`QuantumCorrelatedPostNoise.post_before_environment_trace`](../../Verification/QuantumCorrelatedPostNoise.lean#L125)
- [`QuantumCorrelatedPostNoise.noisy_outcome_some`](../../Verification/QuantumCorrelatedPostNoise.lean#L132)
- [`QuantumCorrelatedPostNoise.noisy_outcome_cp`](../../Verification/QuantumCorrelatedPostNoise.lean#L140)
- [`QuantumCorrelatedPostNoise.noisy_outcome_positive`](../../Verification/QuantumCorrelatedPostNoise.lean#L152)
- [`QuantumCorrelatedPostNoise.noisy_outcome_trace`](../../Verification/QuantumCorrelatedPostNoise.lean#L160)
- [`QuantumCorrelatedPostNoise.noisy_total_trace`](../../Verification/QuantumCorrelatedPostNoise.lean#L168)
- [`QuantumCorrelatedPostNoise.noisy_zero_iff`](../../Verification/QuantumCorrelatedPostNoise.lean#L175)
- [`QuantumCorrelatedPostNoise.noisy_zero_iff_original`](../../Verification/QuantumCorrelatedPostNoise.lean#L182)
- [`QuantumCorrelatedPostNoise.noisy_outcome_sum`](../../Verification/QuantumCorrelatedPostNoise.lean#L189)
- [`QuantumCorrelatedPostNoise.identity_post_refinement`](../../Verification/QuantumCorrelatedPostNoise.lean#L199)
- [`QuantumCorrelatedPostNoise.noisy_product_partial_trace`](../../Verification/QuantumCorrelatedPostNoise.lean#L208)
- [`QuantumCorrelatedPostNoise.noisy_sum_products`](../../Verification/QuantumCorrelatedPostNoise.lean#L217)
- [`QuantumCorrelatedPostNoise.noisy_product_bridge`](../../Verification/QuantumCorrelatedPostNoise.lean#L226)
- [`QuantumCorrelatedPostNoise.noisy_post_interaction_invariant`](../../Verification/QuantumCorrelatedPostNoise.lean#L241)
- [`QuantumCorrelatedPostNoise.noisy_tensor_stages_reduction`](../../Verification/QuantumCorrelatedPostNoise.lean#L249)
- [`QuantumCorrelatedPostNoise.verification_suite`](../../Verification/QuantumCorrelatedPostNoise.lean#L269)

## Limits

One-cycle finite-dimensional semantics; no later interaction with the same memory,
adaptive process tensor, hardware calibration or general classification. Existing
Werner visibility results retain their product-input/channel/readout hypotheses;
they are not re-proved here or extended to arbitrary correlated inputs.
