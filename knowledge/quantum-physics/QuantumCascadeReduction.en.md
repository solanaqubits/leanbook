---
id: QuantumCascadeReduction
language: en
section: quantum-physics
source: Verification/QuantumCascadeReduction.lean
source_sha256: eff7af44d03ee34a938fd623cebd6787800ba392b1034e3526d5798e419bb214
novelty: not-assessed
status: reviewed
---

# QuantumCascadeReduction

[Section](README.md) · [Lean source](../../Verification/QuantumCascadeReduction.lean) ·
[Scope and verification](../../docs/quantum-v4.27.md)

Scalar analysis of the specified Werner transition T(w)=alpha*w, with
alpha=gamma_corr*gamma_bsm*w_fresh and all three factors in [0,1]. The output
operator is not defined by this formula: the independent matrix refinement is
in QuantumWernerCascade.

Theorems establish alpha bounds, preservation of [0,1], nonincrease of visibility
and fidelity for nonnegative inputs, and strict decrease when w>0 and alpha<1.
The complete fixed-point equation is w=0 OR alpha=1. At alpha<1 the unique fixed
point is zero; at alpha=1 every input is fixed. Fidelity equality has the same
classification. There is no improvement threshold for this transition.

Finite constant-parameter iteration is alpha^n*w. A finite varying schedule gives
the product of its multipliers and remains nonincreasing on nonnegative inputs.
Separate Tendsto theorems prove convergence of visibility to zero and fidelity to
1/4 for constant alpha<1. For nonnegative inputs fidelity stays at or above 1/4;
alpha=0 may reach that value after one step. No convergence claim is made for an
arbitrary varying schedule.

## Theorems

- [`QuantumCascadeReduction.alpha_bounds`](../../Verification/QuantumCascadeReduction.lean#L38)
- [`QuantumCascadeReduction.werner_transition_le_id`](../../Verification/QuantumCascadeReduction.lean#L47)
- [`QuantumCascadeReduction.transition_bounds`](../../Verification/QuantumCascadeReduction.lean#L51)
- [`QuantumCascadeReduction.fidelity_monotonicity`](../../Verification/QuantumCascadeReduction.lean#L55)
- [`QuantumCascadeReduction.strict_decay`](../../Verification/QuantumCascadeReduction.lean#L62)
- [`QuantumCascadeReduction.fixed_point_iff`](../../Verification/QuantumCascadeReduction.lean#L69)
- [`QuantumCascadeReduction.unique_fixed_point_at_zero`](../../Verification/QuantumCascadeReduction.lean#L79)
- [`QuantumCascadeReduction.lossless_identity`](../../Verification/QuantumCascadeReduction.lean#L83)
- [`QuantumCascadeReduction.fidelity_equality_iff`](../../Verification/QuantumCascadeReduction.lean#L86)
- [`QuantumCascadeReduction.cascaded_iteration`](../../Verification/QuantumCascadeReduction.lean#L93)
- [`QuantumCascadeReduction.finite_schedule_product`](../../Verification/QuantumCascadeReduction.lean#L107)
- [`QuantumCascadeReduction.visibility_tends_to_zero`](../../Verification/QuantumCascadeReduction.lean#L116)
- [`QuantumCascadeReduction.fidelity_tends_to_quarter`](../../Verification/QuantumCascadeReduction.lean#L121)
- [`QuantumCascadeReduction.fidelity_above_quarter`](../../Verification/QuantumCascadeReduction.lean#L128)
- [`QuantumCascadeReduction.finite_schedule_nonincrease`](../../Verification/QuantumCascadeReduction.lean#L136)
- [`QuantumCascadeReduction.verification_suite`](../../Verification/QuantumCascadeReduction.lean#L152)

## Limits

The scalar law is tied to the stated Werner inputs, depolarizing channels and
perfect readout. It is not a universal fidelity law for CPTP maps, correlated
resources, adaptive feedback or postselection. No purification circuit, retained
memory process tensor, or arbitrary-number-of-rounds operator instrument is
formalized here. Finite iteration and limits concern the proved scalar recurrence.
Counts include auxiliary and registry theorems, not independent scientific results.
