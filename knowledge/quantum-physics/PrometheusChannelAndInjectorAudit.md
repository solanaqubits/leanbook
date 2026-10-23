---
id: PrometheusChannelAndInjectorAudit
language: en
section: quantum-physics
source: Verification/PrometheusChannelAndInjectorAudit.lean
novelty: not-assessed
status: reviewed
source_sha256: f90256d8939c5efcf4b6837a5bc3262a77383bfb2948329714fbddc38ae70324
---

# Single-letter channel information and injector neutron kinetic energy

[Section](README.md) ·
[Lean](../../Verification/PrometheusChannelAndInjectorAudit.lean)

Epsilon249, quantum-physics/prometheus-channel-injector. This module implements
the corrected formal contract of user prompt 7; the related finite experiment
from prompt 8 belongs separately to SimLab.

## Definitions and proved results

The finite transition matrix has a Bool input and erased/zero/one outputs.
Erasure probability e is the same for both inputs. Correct and substituted
delivered bits have probabilities (1-e)(1-p) and (1-e)p. Row nonnegativity and
normalization are proved for e,p in [0,1]. This is a stipulated channel, not a
derivation from a device or a temporal dead-time model.

binaryEntropy p=(-p log p-(1-p)log(1-p))/log2 uses the genuine real logarithm.
For 0<p<1,0<H2(p)<=1 is proved, together with H2(1/2)=1. The upper bound follows
from log x<=x-1. Regression proofs check zero endpoint values using Mathlib's
total real log function.

For input bias b=P(X=1) in [0,1], the output marginal and finite mutual-information
sum are explicit. For 0<e<1 and 0<p<1, the proof establishes

I(X;Y)=(1-e)*(H2((1-b)*p+b*(1-p))-H2(p)).

The entropy bound yields I<=C=(1-e)(1-H2(p)) for every input bias, and uniform
input b=1/2 attains C. This is a proved single-letter maximum over all binary
input distributions for the specified matrix. The maximization theorem uses
interior e,p; the actual scenario inputs satisfy these premises. A separate
uniform-input finite MI sum is also reduced to C.

Earlier conditional-run frequencies become exact scenario parameters:
e=6664/10000,p=34/3336,d=3336/10000>1/3. This does not prove that an empirical
frequency equals an unknown physical probability. H2(p)<9/100 is established
without a numerical oracle: p>1/128 implies -log p<7log2; the complementary
entropy term is at most p; log2>=7/12 follows from 2=(4/3)(3/2) and
log x>=1-1/x. Exact arithmetic then proves 3/10<C<1.

## Code rate and the corrected false requirement

codeRate k n=k/n. If n>0 and 10*k<=3*n, codeRate k n<C follows as an arithmetic
rate-budget certificate. It does not construct a reliable code. A universal
R<=C assertion for arbitrary finite codes is refuted: the one-bit identity
encoder is injective and has R=1>C, but decodes a flipped observation incorrectly.
A regression proves that the stipulated matrix assigns that event positive
probability 17/5000.

Given the separately supplied Fano-style premise k<=n*C+1+error*k, with n>0
and error<1, the algebraic conclusion is R<=(C+1/n)/(1-error). Deriving that
premise from a probabilistic code is not formalized. No asymptotic coding
theorem, operational converse, finite FEC failure probability, or recovery of
all packets is proved. Dead-time correlations are not automatically covered
by a single-letter model.

## Latency and the energy quantity

Milliseconds are used throughout:T=40.410+n/100000+Tdecode. One slot is 10 ns.
For n<=10000 and Tdecode<=1ms,77.921-T>=36.411ms>36ms, hence T<77.921.
The propagation numbers 40.410 and 77.921 are rounded stipulated inputs, not a
reproof of epsilon244's sine-based geometry. Omitted generation, accumulation
and processing latency is not bounded. Real decoder speed is not measured.

For 3000000 neutrons at a stipulated 2.45 MeV each, using the exact conversion
1MeV=1.602176634e-13J, E_neutron=1.17759982599e-6J, with the strict bracket
1.1775e-6<E_neutron<1.1776e-6J. The fraction relative to an incident laser pulse
of 1.6 J is positive and below 1e-5<1. This is only the specified neutrons' kinetic
energy. It is not total reaction energy, deposited energy, electrical output,
or an engineering gain including wall-plug input. The PB11 module is unchanged.

## Verification and evidence

The standard verify command passed: 157 declarations, only propext,
Classical.choice and Quot.sound, no violations. Two live unittest methods
passed without skips: 46 core examples and 5 registry examples. The integration
recipe passed its checks; the parent integrator separately performs final main
reconciliation and the affected gate. This is not a new full beta checkpoint.

Key declarations:transition_normalized, [information_formula](../../Verification/PrometheusChannelAndInjectorAudit.lean#L244),
[single_letter_capacity_maximum](../../Verification/PrometheusChannelAndInjectorAudit.lean#L280), [observed_entropy_lt_nine_percent](../../Verification/PrometheusChannelAndInjectorAudit.lean#L149),
conditional_rate_budget, not_every_finite_rate_below_capacity,
conditional_fano_rate_bound, [latency_gap](../../Verification/PrometheusChannelAndInjectorAudit.lean#L354), [neutron_kinetic_exact](../../Verification/PrometheusChannelAndInjectorAudit.lean#L371),
neutron_fraction_bounds. The registry field is
QuantumPhysicsFullSuite.prometheus_channel. There are no direct Verification
imports. Mathematical or formalization priority has not been assessed.

Errors, repairs, commands and JSON audits are retained in
prometheus-fec-injector-249-evidence/lean-dev. Numerical experiments, physical
channel applicability and source parameters are separate obligations.
Hardware qualification, authorization and the Third Obligation are unchanged.

Independent public validation for this source is recorded in [release v0.7.46](../../docs/release-v0.7.46.en.md).
