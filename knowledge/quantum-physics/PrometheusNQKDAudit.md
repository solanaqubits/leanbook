---
id: PrometheusNQKDAudit
language: en
section: quantum-physics
source: Verification/PrometheusNQKDAudit.lean
novelty: not-assessed
status: reviewed
source_sha256: bd9803d7ded471e727a39cf5f9e75bf836a0836d26e87fde2a2e8cad766d63b1
---

# BB84 interception, independent noise, and limits of universal disturbance

[Section](README.md) · [Lean](../../Verification/PrometheusNQKDAudit.lean)

Stage ε256, batch quantum-physics/prometheus-nqkd-takl. The unchanged
QuantumBB84ProtocolQBER core supplies actual complex 2×1 kets, projectors ket ket†,
Born probabilities Re Tr(Pρ), and a normalized finite joint experiment.

## Exact contract

All Z/X states are normalized; cross-basis overlaps are1/2 and distinct same-basis
states are orthogonal. Overlap<1 does not imply nonorthogonality: zero is an
explicit counterexample. Independent uniform choices and actual Born branches
give P(sift)=1/2, P(error∩sift)=1/8, conditional intercepted QBER=1/4.
An independent honest/attack mixture of weight f∈[0,1] gives f/4. The inherited
results are proved, not assumptions or definitions of the desired answer.

The new normalized noisyLaw is the product of the round law and an independent
Bernoulli bit flip p∈[0,1]. Finite summation derives
QBER=p+(1−2p)f/4=f/4+(1−f/2)p. It exceeds baseline p only when p<1/2 and f>0;
p=1/2 removes the effect and p>1/2 reverses it. Product independence is explicit.
The rearrangement does not prove an Rz implementation or identify this symmetric
noise model with basis-specific phase noise in Python.

For any normalized complex vector v, forgotten complete projective measurement
in either Z/X basis gives wrongReturn=Re Tr((I−vv†)dephase(vv†))=2c(1−c),
c=Re Tr(P0vv†). Strict disturbance needs0<c<1. Known matching orthogonal-basis
measurement is nondisturbing. The complete noninformative instrument
Kx=(√2/2)I has ΣKx†Kx=I, outcome probability1/2 for traceρ=1, and channelρ↦ρ.
Thus not every unauthorized measurement must introduce errors.

For all finite m the scalar IID no-error factor (1−f/4)^m is positive. The new
module proves this algebraic fact; the inherited core constructs the actual IID
sample law for f=1 and proves miss probability (3/4)^m>0. Expected QBER does not
guarantee detection in every finite trial.

## Historical development checks and limits

Standard verify passed291 declarations in the import closure, using only
propext, Classical.choice and Quot.sound. Both new modules have58 Lean examples
in three live methods; adding the existing BB84 regression gives4 passed methods,
no skips. Checks cover exact values, p/f/c endpoints, normalization,
counterexamples and registry exports. CLI integration diffs were reviewed and
applied exactly; affected registry build passed3921 Lake jobs with cache retained.
These are historical development checks; see this release for public validation.

Neutrino Majorana/OAM realization of these qubits, sources, detectors, losses,
authentication, error correction, privacy amplification, collective attacks and
composable finite-key security are not proved. Born's rule is a model postulate.
Hardware eligibility, authorization and the Third Obligation remain unchanged.
Novelty is not assessed.

## Source theorem links

- [born_intercept_quarter](../../Verification/PrometheusNQKDAudit.lean#L42)
- [independent_baseline_qber](../../Verification/PrometheusNQKDAudit.lean#L109)
- [finite_iid_no_error_positive](../../Verification/PrometheusNQKDAudit.lean#L125)
- [pure_wrong_return_exact](../../Verification/PrometheusNQKDAudit.lean#L182)
- [nonorthogonal_return_disturbance](../../Verification/PrometheusNQKDAudit.lean#L196)
- [coin_kraus_complete](../../Verification/PrometheusNQKDAudit.lean#L216)
- [coin_channel_identity](../../Verification/PrometheusNQKDAudit.lean#L223)
- [known_basis_nondisturbance](../../Verification/PrometheusNQKDAudit.lean#L239)

Independent public validation for this source is recorded in [release v0.7.46](../../docs/release-v0.7.46.en.md).
