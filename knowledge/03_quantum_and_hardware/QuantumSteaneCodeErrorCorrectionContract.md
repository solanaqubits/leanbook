---
id: QuantumSteaneCodeErrorCorrectionContract
language: en
section: quantum-physics
source: Verification/QuantumSteaneCodeErrorCorrectionContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 86c65a7c7f821fb8b09ee7faec8785b7c9319a919bc3d78b8c06ceaf1f9610cb
---

# Steane CSS: finite syndromes, codespace and phases

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean)

Stage ε282: requested 281 belongs to threshold tomography. The contract is
finite-dimensional and ideal; noisy measurement and fault-tolerant circuits are excluded.

## Seven fixed positions and two syndromes

`Bit := ZMod 2`, `Word := Fin 7 → Bit`, `Ket := Word → ℂ`: amplitudes are functions
on 128 computational basis words. The rows of H are masks 85,102,120, with positions
0..6 numbered from the least significant bit. Its columns are the seven nonzero
three-bit values 1..7. Row orthogonality, distinct nonzero columns and absence of
nonzero weight-<3 words in ker H are proved.

A binary Pauli label is `(x,z)`. The full syndrome is `(Hx,Hz)`, six bits;
X checks take their sign from Hz, while Z checks use Hx. `SingleError := Fin 3 × Fin 7`
lists 21 canonical errors: kind 0=X,1=Z,2=Y. Their syndromes are distinct and nonzero.
`decodeSyndrome` searches that error list for a matching syndrome; it is an actual
lookup, not an error-id handed to the decoder. Zero syndrome decodes to none,
and `recover` then leaves the input unchanged. No correction promise follows
for errors outside this set.

## Complex operators and the codespace

`xAction` shifts a basis word; `zAction` multiplies its amplitude by the binary
inner-product sign. `pauliAction c x z` explicitly represents c·X^x Z^z.
The scalar c may be any complex value, including 0, so general algebraic lemmas
do not assert unitarity for arbitrary c. Canonical single Y is iXZ. Its square
is I; canonical errors are involutions preserving the sum of squared moduli.
Without i, repeating XZ gives −I. All six actual stabilizer actions are proved
to commute, not merely their binary labels.

`Codespace` is their common +1 eigenspace. Let D be the row space of H.
Its eight words and D+1111111 are disjoint and partition ker H. `rawEncode` is
constant on each coset and zero elsewhere. Every code vector is characterized
by this form. `encode` uses 1/√8, is complex-linear and injective, and preserves
|α|²+|β|². `codespace_exactly_one_qubit` gives a unique coefficient pair (α,β)
for every code vector. This is an explicit one-logical-qubit bridge, not an
inference solely from counting generators. Zero and unnormalized vectors are
allowed; encoding transfers input normalization by isometry.

## Recovery and its precise scope

The decoder identifies each canonical single error, whose involution yields
exact recovery for arbitrary vectors. Interpreting the supplied syndrome as
an ideal check result additionally requires the original `Codespace ψ`:
the actual check eigenvalues of the erroneous code vector are proved separately.
Sequential ideal spectral projectors for the correct syndrome leave that vector
unchanged. This is not an apparatus model, a general noisy recovery channel or
a Knill–Laflamme theorem for all one-qubit CPTP errors. The supported set is
identity plus 21 canonical Pauli errors.

Global phase is invisible to the syndrome. Exact canonical vector recovery cannot
be extended simultaneously to P and −P using the same decoder. Binary labels
provide projective bookkeeping and do not contain the omitted global phase.

## Distance and logical operators

`InCentralizer` means Hx=Hz=0; `InStabilizerLabels` means x,z∈D. Weight counts
the union of the supports of x,z. An explicit operator bridge proves centralizer
representatives commute with the actual checks on arbitrary Ket. Every centralizer label outside the stabilizer
labels has weight≥3, and X-mask 7 supplies such a weight 3 witness. Global scalar
phases are excluded: otherwise −I would give a spurious nontrivial weight 0 example.
Together with the explicit encoding, this establishes [[7,1,3]] in this model.

For stabilizer labels, the specified scalar 1 representative X^x Z^z fixes the code.
An arbitrary phase choice, including a positive tensor-Y representative, need not
have eigenvalue +1. Rows 85 and 102 overlap on two positions, giving an additional
i²=−1 under that replacement; the binary label alone does not certify the sign.

Transversal logicalX/logicalZ use mask 127, commute with the checks, preserve the
code and anticommute with each other. On encode they act as (α,β)↦(β,α) and
(α,β)↦(α,−β). The weight 3 witness acts as logicalX on the code. Two X errors at
positions 0,1 share the syndrome of a single X at position 2: recovery leaves
logical mask 7 and maps encode(α,β) to encode(β,α). This refutes a general two-error
correction promise without contradicting the single-error theorem.

## Evidence and boundaries

The older [QuantumStabilizerCodes](../quantum-physics/QuantumStabilizerCodes.en.md)
uses phase-free lists and truncating zipWith operations; its commuting predicate
does not establish a closed group. It remains separate context, not a direct
import or proof of the new seven-qubit codespace.

The finite Python specification oracle is separate supporting computation,
not a Lean proof or physical experiment. Lean `decide` is kernel-checked;
native_decide is not used. No measured hardware metrics, ancilla circuit,
noisy syndrome extraction, fault tolerance or threshold theorem is claimed.
Novelty is not assessed. Publication, authorization and the Third Obligation are unchanged.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [rows_orthogonal](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L52)
- [columns_nonzero](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L54)
- [columns_injective](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L56)
- [hamming_minimum](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L61)
- [stabilizers_commute](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L591)
- [codespace_characterization](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L207)
- [rowspace_card](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L171)
- [coset_card](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L176)
- [encoding_isometry](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L263)
- [encoding_injective](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L286)
- [encoding_add](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L295)
- [encoding_smul](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L300)
- [codespace_exactly_one_qubit](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L306)
- [single_syndrome_decodes](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L341)
- [single_syndromes_unique](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L344)
- [identity_syndrome_decodes](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L349)
- [canonical_y_involution](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L360)
- [single_error_correction](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L566)
- [identity_exact_recovery](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L390)
- [error_stabilizer_eigenvalues](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L409)
- [single_error_correct_projection](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L612)
- [single_error_isometry](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L655)
- [steane_code_distance](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L554)
- [logical_weight_three_witness](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L516)
- [stabilizer_label_fixes_code](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L533)
- [centralizer_preserves_codespace](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L540)
- [centralizer_commutes_checks](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L703)
- [weight_three_acts_logically](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L548)
- [logical_anticommutation](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L444)
- [logical_commutes_stabilizers](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L448)
- [logicalX_on_encoding](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L461)
- [logicalZ_on_encoding](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L475)
- [logical_operators_preservation](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L634)
- [two_error_alias](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L673)
- [two_error_miscorrection](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L677)
- [unsigned_xz_square](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L714)
- [verification_suite](../../Verification/QuantumSteaneCodeErrorCorrectionContract.lean#L755)
