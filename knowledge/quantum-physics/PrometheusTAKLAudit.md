---
id: PrometheusTAKLAudit
language: en
section: quantum-physics
source: Verification/PrometheusTAKLAudit.lean
novelty: not-assessed
status: reviewed
source_sha256: 6665473f8d56882e4fb887558888e75c09f8a074bf4f398e42fae24bbd5839a2
---

# T-AKL phase invariance, conditional state density, and a ring model

[Section](README.md) · [Lean](../../Verification/PrometheusTAKLAudit.lean)

Stage ε257, batch quantum-physics/prometheus-nqkd-takl. This formalizes
conditional golden-rule algebra and a supplied nonrelativistic scalar ring model,
not a weak-interaction QFT Lagrangian derivation.

## Exact contract

Γ=(2π/ℏ)‖M‖²ρ. The complex factor exp(iφ) has unit norm, so a global amplitude
phase leavesΓ unchanged at fixedρ. Forℏ>0,M≠0,ρ0>0 and the explicit premise
|δρ|≤ερ0, the relative bound|Γ(ρ0+δρ)−Γ(ρ0)|/Γ(ρ0)≤ε follows with positive
baseline denominator. Monotonicity follows only from a separately assumed
monotone density and a fixed nonnegative prefactor.

The positive phenomenological densityρ0(1+a(1−cosφ)),ρ0>0,a>0, is2π-periodic
but not globally monotone: values at0 and2π areρ0, while the value atπ is
ρ0(1+2a)>ρ0. A positive prefactor preserves this counterexample forΓ.
This is not a calculated beta-decay final-state density. At a=0 there is no effect.

The supplied signed AC parameter is2πR E μ/(ℏc²); field reversal changes its sign.
Radial geometry, effective moment and units are assumptions. The scalar
L=Iω²/2+aω, canonical p=Iω+a and H=(p−a)²/(2I) satisfy the Legendre identity
pω−L=H forI≠0; physical interpretation requiresI>0.

The supplied spectrum E_l=ℏ²/(2mR²)(l−φ/(2π))² satisfies
E_(l+1)(φ+2π)=E_l(φ). This is family periodicity under integer relabeling,
not fixed-level periodicity. Nonnegativity holds for m>0. A physical ring requires
R>0 andℏ>0; Lean's total division does not substitute for these premises.
No operator spectral problem, self-adjointness or boundary conditions are derived.

For this explicit density model, |ΔΓ|/Γ0 ≤ a·φ_AC(E)²/2 is also derived
for a≥0 using the global inequality1−cosφ≤φ²/2. This is an exact model-specific
E² bound, not a small-angle approximation or a derived physical DOS response.
The Python multiplier1+α(cosφ−1) uses a=−α, so this corollary applies to α≤0.
No formal refinement relation to Python is established.

## Historical development checks and limits

Standard verify passed48 declarations, with only propext, Classical.choice and
Quot.sound. Together with NQKD there are58 new Lean examples and3 live methods;
adding the existing BB84 regression gives4 passed methods, no skips. Tests cover
both signs ofδρ, zero amplitude, a=0, periodicity/nonmonotonicity, orientation,
concrete Legendre values and registry exports. Both CLI integration diffs were
reviewed and applied exactly; the affected registry built successfully in3921
Lake jobs with cache retained. Final reconciled verification is performed under
the separate integration lock.

Ring center-of-mass state density is not identified with beta-decay final-state
density. Neutron lifetime modification, confinement, experimental sensitivity,
new interactions and full QFT are not established. Links to SimLab sensitivity
branches are conditional. Hardware eligibility, authorization and the Third
Obligation remain unchanged. Novelty is not assessed.

## Source theorem links

- [global_phase_rate_invariant](../../Verification/PrometheusTAKLAudit.lean#L41)
- [conditional_relative_rate_bound](../../Verification/PrometheusTAKLAudit.lean#L56)
- [density_three_values](../../Verification/PrometheusTAKLAudit.lean#L89)
- [density_not_monotone](../../Verification/PrometheusTAKLAudit.lean#L102)
- [rate_not_monotone](../../Verification/PrometheusTAKLAudit.lean#L109)
- [orientation_reversal](../../Verification/PrometheusTAKLAudit.lean#L125)
- [legendre_identity](../../Verification/PrometheusTAKLAudit.lean#L162)
- [flux_relabel](../../Verification/PrometheusTAKLAudit.lean#L173)
- [periodic_ac_relative_bound](../../Verification/PrometheusTAKLAudit.lean#L132)

Independent public validation for this source is recorded in [release v0.7.46](../../docs/release-v0.7.46.en.md).
