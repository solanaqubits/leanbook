# Quantum v4.24 — post noise on correlated joint inputs

Local scoped/gamma candidate on `f038e0e706ba2b2a412533dfd93a0ae9b8cc8589`
(v4.23), branch `quantum-correlated-post-v424`. Published Leanbook `v1.0.0`
is unchanged. No toolchain or dependency update is included.

[Exact inventory](quantum-v4.24-inventory.json) ·
[Verification record](quantum-v4.24-verification.json)

## Why this addition is distinct

The earlier proposal repeated results already present in v1.0.0:
`QuantumGateNoiseComposition` supplies system-only composite Kraus operators,
CP/PSD and causal trace invariance; `QuantumNoisyVisibility` and
`QuantumLocalNoisySwapping` prove the specified Werner visibility product.
`QuantumInternalBSMNoise` handles the stated analyzer insertion cuts. These
proofs are reused, not reclassified as new results.

The new module `QuantumCorrelatedPostNoise` extends the **correlated joint-input**
instrument of v4.21. Its argument is an arbitrary `JointFourDensity e`; it need
not be a product with any fixed environment state. The post channel depends on
the delivered classical message and acts on AD only. It has no later interaction
with the same environment. The reject branch receives no correction noise.

## Contracts

- `postPath` and `microKraus` retain the chronological path, environment selector
  and post-channel Kraus label. Their size is 4 by (16 times environment dimension),
  not 4 by 16. `noisy_micro_weighted` and `noisy_micro_kraus` identify the actual
  map with both the weighted and square-root-absorbed operator sums.
- `noisy_micro_cp` and `noisy_outcome_cp` use `IsCPMap` with arbitrary finite
  ancillary spaces. Positivity is separately explicit in `noisy_outcome_positive`.
- `noisyJointLinear`, `noisy_outcome_sum` and `noisy_sum_products` preserve complex
  linearity. The finite-product-sum identity is algebraic; arbitrary complex
  coefficients are not presented as physical mixture weights.
- `noisy_micro_trace` and `noisy_outcome_trace` preserve microscopic and observed
  branch traces for every joint matrix. The output channel may change or erase
  matrix distinctions, but cannot change these probabilities on density inputs.
- `noisy_total_trace` reuses the earlier explicit hypothesis
  `(ideal ss).matrix = extend (embedBC analysisUnitary)` for five-outcome balance.
  The hypothesis is not silently discarded or confused with noise-free dynamics.
- `noisy_zero_iff` and `noisy_zero_iff_original` use PSD to prove that null branches
  remain null and nonzero PSD branches cannot become zero under CPTP post noise.
- `post_before_environment_trace` equates local AD processing before environment
  reduction with processing the reduced matrix. This is an independent output
  channel, not a repeated joint interaction with the memory.
- `noisy_product_partial_trace` reuses v4.20 on product input without an analyzer
  hypothesis. `noisy_product_bridge` adds that hypothesis and identifies the
  result with the old `noisyOutcome (effectivePre ss σ) post` on 4-by-16 system input.
- `identity_post_refinement`, `noisy_post_interaction_invariant` and
  `noisy_tensor_stages_reduction` preserve the earlier instrument and both v4.23
  refinements. Arbitrary preceding joint dynamics are not thereby declared
  reducible to the initial system marginal.

## Regression scope

New live fixtures exercise a 4-by-48 operator, an additional three-dimensional
ancilla, the product bridge and v4.23 interaction refinement. They test that
arbitrary post noise preserves the GHZ witness's probability gap (1/2 versus 0)
and its zero branch. Conversely, complete depolarization erases the two Bell
witness output matrices whose traces already agree. Registry export is tested.
Existing v4.22/v4.23, gate-noise and local-post-noise fixtures are retained,
including exact Werner fidelity values under their specified hypotheses.

The module has 23 named theorem declarations and 30 named exports including
six definitions and its suite structure. Helper lemmas and the registry suite
are included; these counts are not independent scientific results.

## Limits

This does not extend the visibility product to arbitrary correlated inputs or
arbitrary noise. Product Werner states, specified depolarizing channels and ideal
readout remain assumptions of those earlier results. General CPTP post noise is
not necessarily fidelity-decreasing or injective. No hardware calibration,
adaptive process tensor or classification of all interactions is supplied.

Validation is scoped/gamma: strict module verification with imported axiom
closure, incremental root integration, targeted live tests and an independent
compiled-project axiom audit. A fresh full `verify-all`, full unittest discovery,
clean build or remote CI run is not claimed. Historical full validation remains
attached to v4.21 and its documented multi-run history. Source hashes and actual
commands are recorded separately in the verification artifacts.
