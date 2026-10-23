---
id: PhotonicsMachZehnderChiralContract
language: en
section: quantum-physics
source: Verification/PhotonicsMachZehnderChiralContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 4ad8a2e9fb81ae52dd443b18b36543d99d9c0df6657be6544d5aa832804bc39a
---

# Ideal two-mode MZI: intensity and phase routing

[Section](README.md) · [Lean](../../Verification/PhotonicsMachZehnderChiralContract.lean)

Stage ε264. `Amp2 := ℂ × ℂ`; `intensity (a,b) = normSq a + normSq b`.
This is a sum of squared complex moduli, not the default product supremum norm.
Amplitudes are normalized; no calibration in joules or watts is supplied.

## Exact operators and results

`chiralMirror (a,b) = (a,-b)` is a stipulated sign flip on the second component.
`phaseShift φ (a,b) = (exp(iφ)*a,b)` acts on the first arm, for φ : ℝ.
`beamSplitter` is the normalized Hadamard H(a,b)=((a+b)/√2,(a−b)/√2).
`mziStep φ = H ∘ phaseShift φ ∘ H`. The argument φ is dimensionless;
a physical phase interpretation commonly uses radians.

The mirror and H are involutions. All three components and the MZI preserve
`intensity` for every complex input. The module proves complex linearity,
composition `mziStep φ (mziStep ψ v) = mziStep (φ+ψ) v`, left and right
inverses at phase −φ, and preservation of `intensity (u−v)`, the squared
Euclidean distance in amplitude coordinates.

For input (1,0), the amplitudes are derived from the composition:
((exp(iφ)+1)/2,(exp(iφ)−1)/2). Their intensities are (1+cosφ)/2 and
(1−cosφ)/2. At φ=0 the action is the identity; at φ=π the exact action
is (−b,−a), sending (1,0) to (0,−1). Port intensities swap, while the
amplitude equality retains the global minus sign. The separate construction
H ∘ chiralMirror ∘ H gives the literal swap (b,a), since the mirror flips
the second component rather than the first.

## Existing project result

[PhotonicsBeamSplitterPhaseShift](../03_quantum_physics_and_optics/PhotonicsBeamSplitterPhaseShift.md)
already formalizes a more general complex splitter parameterized by T and
B† Pφ B. This module provides a narrower Hadamard/sign-flip interface and
does not claim the project's first MZI proof. At T=1/2 the port-intensity
laws agree, but different phase conventions do not silently identify complex
outputs or operators. Novelty remains `not-assessed`.

## Limits

The name `chiralMirror` does not establish material chirality, reflector
geometry or fabrication. `mzi_passive_energy_conservation` states precisely
preservation of the defined `intensity`. It supplies no physical energy budget
and proves no zero cost for control, computation, detection or phase setting.
Loss, noise, dispersion, polarization, detectors, Maxwell equations and the
full Fock space are outside this model.

There are no direct Verification imports; the module uses Mathlib complex/
trigonometric APIs and ring. Device correspondence requires a separate
argument. Hardware eligibility, authorization and the Third Obligation
remain unchanged.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Theorems

- [chiralMirror_preserves_intensity](../../Verification/PhotonicsMachZehnderChiralContract.lean#L58)
- [mirror_between_splitters](../../Verification/PhotonicsMachZehnderChiralContract.lean#L69)
- [phaseShift_preserves_intensity](../../Verification/PhotonicsMachZehnderChiralContract.lean#L61)
- [beamSplitter_preserves_intensity](../../Verification/PhotonicsMachZehnderChiralContract.lean#L74)
- [mzi_passive_energy_conservation](../../Verification/PhotonicsMachZehnderChiralContract.lean#L80)
- [mzi_comp](../../Verification/PhotonicsMachZehnderChiralContract.lean#L132)
- [mzi_inverse](../../Verification/PhotonicsMachZehnderChiralContract.lean#L144)
- [mzi_difference_intensity](../../Verification/PhotonicsMachZehnderChiralContract.lean#L151)
- [mzi_input_amplitudes](../../Verification/PhotonicsMachZehnderChiralContract.lean#L156)
- [mzi_constructive_destructive_routing](../../Verification/PhotonicsMachZehnderChiralContract.lean#L175)
- [mzi_pi](../../Verification/PhotonicsMachZehnderChiralContract.lean#L140)
- [verification_suite](../../Verification/PhotonicsMachZehnderChiralContract.lean#L206)
- [mzi_routing_half_angles](../../Verification/PhotonicsMachZehnderChiralContract.lean#L180)
- [phaseShift_pi](../../Verification/PhotonicsMachZehnderChiralContract.lean#L126)
