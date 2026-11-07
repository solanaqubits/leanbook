---
id: QuantumCliffordTwirl
language: en
section: quantum-physics
source: Verification/QuantumCliffordTwirl.lean
source_sha256: 8dc34e2f8f29db84d47042091c6938b9c9beda7fbed2a479b6adebf41271f0c6
novelty: not-assessed
status: reviewed
---

# QuantumCliffordTwirl

[Section](README.md) · [Scope](../../docs/quantum-v4.29.md) ·
[Source](../../Verification/QuantumCliffordTwirl.lean)

Explicit finite local ensemble: four Pauli operations followed by three powers
of a unitary Clifford cycle, with conjugate gates on Bob. Matrix computations
prove the action on arbitrary inputs, complex linearity, CP, trace and target
overlap preservation. The formula is derived from the ensemble, not assumed.
Pauli-only dephasing is separated from equalization of the other three Bell weights.

## Theorems

- [`QuantumCliffordTwirl.cycle_unitary`](../../Verification/QuantumCliffordTwirl.lean#L26)
- [`QuantumCliffordTwirl.projector_entry`](../../Verification/QuantumCliffordTwirl.lean#L59)
- [`QuantumCliffordTwirl.cycle_phiPlus`](../../Verification/QuantumCliffordTwirl.lean#L66)
- [`QuantumCliffordTwirl.cycle_phiMinus`](../../Verification/QuantumCliffordTwirl.lean#L77)
- [`QuantumCliffordTwirl.cycle_psiPlus`](../../Verification/QuantumCliffordTwirl.lean#L88)
- [`QuantumCliffordTwirl.cycle_psiMinus`](../../Verification/QuantumCliffordTwirl.lean#L99)
- [`QuantumCliffordTwirl.cycle_projector`](../../Verification/QuantumCliffordTwirl.lean#L110)
- [`QuantumCliffordTwirl.pauli_unitary`](../../Verification/QuantumCliffordTwirl.lean#L120)
- [`QuantumCliffordTwirl.pauli_dephasing_row0`](../../Verification/QuantumCliffordTwirl.lean#L130)
- [`QuantumCliffordTwirl.pauli_dephasing_row1`](../../Verification/QuantumCliffordTwirl.lean#L139)
- [`QuantumCliffordTwirl.pauli_dephasing_row2`](../../Verification/QuantumCliffordTwirl.lean#L148)
- [`QuantumCliffordTwirl.pauli_dephasing_row3`](../../Verification/QuantumCliffordTwirl.lean#L157)
- [`QuantumCliffordTwirl.pauli_dephasing`](../../Verification/QuantumCliffordTwirl.lean#L166)
- [`QuantumCliffordTwirl.bellMass_total`](../../Verification/QuantumCliffordTwirl.lean#L176)
- [`QuantumCliffordTwirl.target_bellMass`](../../Verification/QuantumCliffordTwirl.lean#L181)
- [`QuantumCliffordTwirl.cycle_twirl_projector`](../../Verification/QuantumCliffordTwirl.lean#L187)
- [`QuantumCliffordTwirl.cycle_twirl_sum`](../../Verification/QuantumCliffordTwirl.lean#L203)
- [`QuantumCliffordTwirl.twirl_formula`](../../Verification/QuantumCliffordTwirl.lean#L211)
- [`QuantumCliffordTwirl.cycle_family`](../../Verification/QuantumCliffordTwirl.lean#L226)
- [`QuantumCliffordTwirl.cp_comp`](../../Verification/QuantumCliffordTwirl.lean#L231)
- [`QuantumCliffordTwirl.twirl_cp`](../../Verification/QuantumCliffordTwirl.lean#L237)
- [`QuantumCliffordTwirl.twirl_trace`](../../Verification/QuantumCliffordTwirl.lean#L245)
- [`QuantumCliffordTwirl.twirl_overlap`](../../Verification/QuantumCliffordTwirl.lean#L250)
- [`QuantumCliffordTwirl.twirl_add`](../../Verification/QuantumCliffordTwirl.lean#L262)
- [`QuantumCliffordTwirl.twirl_smul`](../../Verification/QuantumCliffordTwirl.lean#L265)
- [`QuantumCliffordTwirl.localPair_mul`](../../Verification/QuantumCliffordTwirl.lean#L270)
- [`QuantumCliffordTwirl.cycle_clifford`](../../Verification/QuantumCliffordTwirl.lean#L276)
- [`QuantumCliffordTwirl.bell_complete`](../../Verification/QuantumCliffordTwirl.lean#L286)
- [`QuantumCliffordTwirl.twirl_isotropic_formula`](../../Verification/QuantumCliffordTwirl.lean#L294)
- [`QuantumCliffordTwirl.verification_suite`](../../Verification/QuantumCliffordTwirl.lean#L310)
