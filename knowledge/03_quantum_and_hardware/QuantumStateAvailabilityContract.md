---
id: QuantumStateAvailabilityContract
language: en
section: quantum-physics
source: Verification/QuantumStateAvailabilityContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 1d2c65ea39ae6601c73758c3036aa7d7a85b1c990438cf36cf87d4c3e1ac5e79
---

# Ideal teleportation and conditional quantum-state release

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumStateAvailabilityContract.lean)

Stage ε279: requested ε278 belongs to the parallel thermal/finite-key stream.
Complex amplitudes describe a finite-dimensional ideal model. Physical NV memory,
certificate authenticity and delivery timing are not qualified by this contract.

## Bell projection and recovery

`QubitState := ℂ × ℂ`. Normalization means `qubitNormSq ψ = 1`, using the sum
of squared moduli rather than the default sup norm on a product type.
`initialState ψ` places ψ on the first qubit and a supplied Φ+ pair on the other
two. `TripleKet` has three Fin 2 indices. Contraction with a conjugated Bell ket
and `bellProject` are defined by finite sums, not by a probability table.

The four Bell kets are proved orthonormal. The source decomposes into four
projections. Each projection equals
`(1/2) • normalizedPost m ψ`, with Born weight `qubitNormSq ψ / 4`.
For normalized inputs every outcome has probability 1/4. The normalized
conditional branch is `bellKet m ⊗ bobBranch m ψ`.

Bob's branches are Iψ, Zψ, Xψ and XZψ. For Ψ− this is (−β,α), so inverse
correction ZX acts as (β,−α). Repeating XZ would produce −ψ, not literal ψ.
`teleportation_exact_recovery` and its reverse hold for arbitrary amplitudes,
without normalization. Corrections are complex-linear, preserve the sum of
squared moduli and form `correctionLinearEquiv` with the explicit inverse branch.
This is an exact isometry for the specified norm, not a physical-gate claim.

Explicit adapters connect branches and corrections to the previous
[QuantumTeleportationProtocol](../07_quantum_physics_and_optics/QuantumTeleportationProtocol.en.md).
The new projection model derives branches and Born weights; the older card
correctly describes its narrower prescribed-branch interface.

## Reduced states without a classical outcome

`senderReduced` and `bobReduced` are finite partial traces of the pure three-qubit
state. After conditional projection, Alice's first, original qubit has I₂/2
for every normalized ψ (`no_cloning_collapse`). This is local input independence;
it neither destroys information in the global state nor itself constitutes the
general no-cloning theorem. Alice's two qubits jointly occupy the selected Bell state.

Bob's conditional density is that of `bobBranch m ψ`. Averaging all four branches
with their derived weights and without the outcome gives I₂/2
(`bob_unconditioned_mixed`). `classical_channel_requirement` restates that precise
result. In addition, `no_branch_oblivious_decoder` excludes one function recovering
all arbitrary inputs from the branch alone without its label. These results do not
establish relativistic signalling speed, waiting time or all physical protocols.

`separate_no_universal_cloning` reuses
[QuantumNoCloningUnitary](../03_quantum_physics_and_optics/QuantumNoCloningUnitary.md):
no single unitary with one fixed normalized blank copies the density matrices of
all normalized pure qubits. General CPTP, approximate and probabilistic cloners
are outside that reused contract. It is logically separate from a software refusal.

## Release policy and logical NV embedding

`QSAStatus` contains a trusted `pairCertified` Bool and `reportedOutcome : Option`.
`qsaTransition status received` applies the reported correction to the supplied
received value. Having an output is equivalent to a true flag and a present label;
this characterizes the release policy, not physical state availability. A false
flag or missing label yields None.

Exact `some ψ` requires received to be ideal branch m, the flag to be true and
the reported label to equal some m. A wrong label can pass the gate and produce
the wrong state. For particular inputs a wrong label can accidentally recover
the state, so the reverse implication from a correct output to a correct label
is not claimed. The Bool and classical message are not authenticated.

`encodeNV (α,β)=(α,0,β)` uses the existing `CoherentAmp` from
[QuantumDiamondNVInterfaceContract](QuantumDiamondNVInterfaceContract.md).
`decodeNV ∘ encodeNV = id`, the embedded intensity equals qubitNormSq, and exact
recovery is preserved by encoding. This describes a logical two-dimensional
subspace, not physical NV writing, storage, readout, coherence time or calibration.

## Distinct scenarios

[PhotonicsQuantumTeleportation](../03_quantum_physics_and_optics/PhotonicsQuantumTeleportation.md)
models a particular passive optical instrument with two distinguishable successful
branches and total postselected success 1/2. The complete ideal four-outcome Bell
measurement here is a different scenario; it does not raise that optical success
rate to 100%. This source supplies scope comparison, not a direct import.

The ideal resource, projective measurement, Born interpretation and correct known
outcome are model conditions. There is no entanglement certification, authenticated
channel, loss/noise model, physical control-pulse or energy analysis, or universal
identification of QSA with physical availability. Novelty is not assessed.
Publication, hardware authorization and the Third Obligation are unchanged.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [bell_orthonormal](../../Verification/QuantumStateAvailabilityContract.lean#L97)
- [bell_contraction_formula](../../Verification/QuantumStateAvailabilityContract.lean#L91)
- [bell_projection_formula](../../Verification/QuantumStateAvailabilityContract.lean#L102)
- [canonical_bell_decomposition](../../Verification/QuantumStateAvailabilityContract.lean#L109)
- [normalized_post_norm](../../Verification/QuantumStateAvailabilityContract.lean#L136)
- [outcome_probability_scaling](../../Verification/QuantumStateAvailabilityContract.lean#L142)
- [outcome_probability_quarter](../../Verification/QuantumStateAvailabilityContract.lean#L149)
- [teleportation_exact_recovery](../../Verification/QuantumStateAvailabilityContract.lean#L159)
- [correction_right_inverse](../../Verification/QuantumStateAvailabilityContract.lean#L163)
- [correction_add](../../Verification/QuantumStateAvailabilityContract.lean#L167)
- [correction_smul](../../Verification/QuantumStateAvailabilityContract.lean#L171)
- [teleportation_isometry](../../Verification/QuantumStateAvailabilityContract.lean#L175)
- [sender_reduced_scaling](../../Verification/QuantumStateAvailabilityContract.lean#L197)
- [no_cloning_collapse](../../Verification/QuantumStateAvailabilityContract.lean#L207)
- [bob_reduced_post](../../Verification/QuantumStateAvailabilityContract.lean#L212)
- [bob_unconditioned_mixed](../../Verification/QuantumStateAvailabilityContract.lean#L226)
- [no_branch_oblivious_decoder](../../Verification/QuantumStateAvailabilityContract.lean#L236)
- [legacy_branch_adapter](../../Verification/QuantumStateAvailabilityContract.lean#L253)
- [legacy_correction_adapter](../../Verification/QuantumStateAvailabilityContract.lean#L258)
- [separate_no_universal_cloning](../../Verification/QuantumStateAvailabilityContract.lean#L267)
- [qsa_register_availability](../../Verification/QuantumStateAvailabilityContract.lean#L286)
- [qsa_exact_output](../../Verification/QuantumStateAvailabilityContract.lean#L293)
- [qsa_missing_certificate](../../Verification/QuantumStateAvailabilityContract.lean#L298)
- [qsa_uncertified_pair](../../Verification/QuantumStateAvailabilityContract.lean#L302)
- [nv_logical_roundtrip](../../Verification/QuantumStateAvailabilityContract.lean#L313)
- [nv_embedding_isometry](../../Verification/QuantumStateAvailabilityContract.lean#L315)
- [nv_encoded_recovery](../../Verification/QuantumStateAvailabilityContract.lean#L319)
- [classical_channel_requirement](../../Verification/QuantumStateAvailabilityContract.lean#L323)
- [verification_suite](../../Verification/QuantumStateAvailabilityContract.lean#L365)
