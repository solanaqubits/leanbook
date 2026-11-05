---
id: QuantumLocalNoisySwapping
language: en
section: quantum-physics
source: Verification/QuantumLocalNoisySwapping.lean
source_sha256: 668953678a1213d95c4bde11244f98594954b065663cde7fb504d9c67631dea3
novelty: not-assessed
status: reviewed
---

# QuantumLocalNoisySwapping

[Section](README.md) · [Lean source](../../Verification/QuantumLocalNoisySwapping.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

D-only post-noise refines the pair-noise visibility law on Bell-diagonal inputs.
The agreement is not extended to arbitrary inputs: a product-state counterexample
and a general marginal criterion delimit the contract.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `traceD_sum`
- `traceD_smul`
- `traceD_bell`
- `bell_mixture_marginal`
- `local_equals_pair_on_bell_mixture`
- `local_equals_pair_on_density`
- `local_depolarizing_isotropic`
- `local_noisy_visibility_matrix`
- `local_noisy_refines_pair_model`
- `local_noisy_visibility_fidelity`
- `local_noisy_visibility_trace`
- `local_noisy_visibility_positive`
- `product_zero_positive`
- `product_zero_trace`
- `product_zero_marginal_not_mixed`
- `local_and_pair_noise_differ_on_product`
- `identity_endpoint_agrees`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.
