---
id: PrometheusFiniteBlockAudit
language: en
section: quantum-physics
source: Verification/PrometheusFiniteBlockAudit.lean
novelty: not-assessed
status: reviewed
source_sha256: d2f6990a11251f3c69d25af600bf385e4212ac35c60b708e614330ef8b38a883
---

# A constructive finite-block repetition-code guarantee

[Section](README.md) ·
[Lean](../../Verification/PrometheusFiniteBlockAudit.lean)

Epsilon251, quantum-physics/prometheus-finiteblock. This implements the corrected
finite-block contract of prompt 11; numerical block scans and prompt 12's thermal
and differential timing studies are separate SimLab artifacts.

## Exact channel, code and receiver

The stipulated erasure probability is e=6664/10000 and the conditional substitution
probability is p=10192/1000000. The latter is an exact decimal scenario parameter;
it is not the earlier ratio 34/3336, nor a proved unknown physical probability.
Noise takes three values with masses e, (1-e)(1-p), (1-e)p. Their nonnegativity
and sum one are proved. Full finite-word masses are products: IID is an explicit
model definition, not inferred from identical marginals. Nested products cover
all repetitions and all payload bits. These distributions are proved normalized.

repeatEncode repeats every bit r times and has k*r channel positions. It is
injective for r>0. The channel observation is Option Bool, with none for erased
and the transmitted or complemented bit otherwise. The actual decoder receives
only these observations, sums +1 for observed true and -1 for observed false,
and returns the majority bit, or none on a tie. Ground truth enters probability
evaluation, not decoding. A failure includes both a wrong bit and a decoder
erasure. Packet failure is an existential bit failure, equivalently a decoded
packet different from the vector of correct delivered bits.

bitFailureProbability and packetFailureProbability are exact finite sums of
normalized mass times the indicator of actual decoder failure. Their values
are proved in [0,1]. No desired PER bound is a premise.

## Finite achievability proof

For each noise word, define the integer score flipped-count minus correct-count.
The actual decoder fails exactly when this score is nonnegative (ties included).
Its indicator is at most 10^score. Factorization of the finite product expectation
gives the one-use weighted mass

m=e+(1-e)*((1-p)/10+10*p)=572984771/781250000=0.73342050688<3/4.

Thus for every transmitted bit P(failure)<=m^r<=(3/4)^r. A finite union bound
applied to the actual packet distribution gives, for every message,

PER_r(message)<=k*(3/4)^r.

In particular, r=100 and k<=200 imply PER<1e-9. The exact rational certificate
200*(3/4)^100<1e-9 is checked by the kernel, not by Monte Carlo, floating point,
or a numerical decision oracle. Its approximate size is 6.4144e-11; a regression
also proves the strict rational upper bound 6.5e-11.

| Channel uses n | Payload bits k | Repeats r | Rate k/n | Certified PER |
| --- | --- | --- | --- | --- |
| 1000 | 10 | 100 | 0.01 | <1e-9 |
| 5000 | 50 | 100 | 0.01 | <1e-9 |
| 10000 | 100 | 100 | 0.01 | <1e-9 |
| 20000 | 200 | 100 | 0.01 | <1e-9 |

This is a constructive nonasymptotic guarantee for a specified code, not an
optimal achievable rate, normal-dispersion upper bound or PPV theorem. A normal
approximation alone is not a rigorous finite PER certificate. These payloads
vary with n and are explicitly not the separate fixed-256-bit benchmark. At
n<=20000, 256 payload bits allow only 78 complete repetitions; the coarse bound
256*(3/4)^78 is proved larger than 1e-9. Failure of this sufficient bound to
certify the target is not a lower bound on the true PER or an impossibility proof.

## Independence counterexample and scope

A second channel draws noise once and reuses it at all 100 positions. Each
individual position has exactly the same marginal mass as above, yet the actual
majority decoder's failure probability is 52328129/78125000>1/2 for either bit.
This proves that the IID hypothesis cannot be replaced by matching marginals.
Dead time, burst correlations, pointing jitter and device physics do not inherit
the repetition guarantee without a justified coupling to the stipulated model.
No processing latency, decoder runtime, FEC implementation refinement, physical
link qualification, hardware authorization or Third Obligation change follows.

## Verification and evidence

The standard verify passed: 132 declarations, only propext, Classical.choice
and Quot.sound, no violations. Two live unittest methods passed with no skips:
44 core Lean examples and 5 registry examples. Integration passed the strict
root build (3934 Lake jobs, using the cache) and MasterSuite closure audit
(34337 declarations). These overlapping declaration counts are not additive.

Key declarations: product_mass_normalized, product_expectation,
[decode_failure_iff](../../Verification/PrometheusFiniteBlockAudit.lean#L171), indicator_failure_le_weight, likelihood_expectation,
bit_failure_bound, [packet_failure_bound](../../Verification/PrometheusFiniteBlockAudit.lean#L282), [repeated_packet_per_lt](../../Verification/PrometheusFiniteBlockAudit.lean#L312),
repeat_encoder_injective, packet_probability_bounds, [shared_draw_failure_exact](../../Verification/PrometheusFiniteBlockAudit.lean#L346).
The registry exports QuantumPhysicsFullSuite.prometheus_finiteblock. There are
no direct Verification imports. Mathematical/formalization priority is not assessed.
Errors, fixes, commands and audit reports are preserved in
prometheus-finiteblock-251-evidence/lean-dev. Final reconciliation and affected
checks on main are performed separately by the parent integrator; this module's
local check is not a new whole-library beta checkpoint.

Independent public validation for this source is recorded in [release v0.7.46](../../docs/release-v0.7.46.en.md).
