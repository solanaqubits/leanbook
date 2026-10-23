---
id: DataAvailabilitySamplingContract
language: en
section: cryptography
source: Verification/DataAvailabilitySamplingContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 017861e04c443db54b7291b85e7a85951d3fec811b2ced0e914a89b0adb7fb19
---

# Polynomial reconstruction and a finite DAS model

[Section](../cryptography/README.md) · [Lean](../../Verification/DataAvailabilitySamplingContract.lean)

Stage ε277: the requested ε276 belongs to Ready/Prepared. This contract concerns
classical coding and sampling probability, not quantum-state transport.

## Count threshold and polynomial proof

`RSBlockParams` specifies k,n:ℕ, k>0, n=2k. `BlockAvailabilityState` stores
availableShards≤n. `isRecoverable` means k≤availableShards by definition;
`mds_recovery_threshold` unfolds this predicate rather than proving decoding.
Count insufficiency is equivalent to more than k erasures, n−availableShards>k.

The actual algebraic component works over an arbitrary field F. For a finite
index set `selected`, nodes `ι→F` injective on that set, and selected.card≥k,
two degree-<k polynomials agreeing at those nodes are equal
(`mds_unique_of_card_le`). Degree is `Polynomial.degree`, with −∞ for the zero
polynomial. This is not a count-only check.

`mds_interpolate_authentic` assumes an existing degree-<k polynomial p and
values i=p.eval(nodes i) on selected. With the same distinct-node and count
premises, it proves `Lagrange.interpolate selected nodes values = p`.
`mds_existsUnique_authentic` gives a unique polynomial with those evaluations,
using the explicit interpolant as its existence witness. Authenticity is
assumed, not established by a cryptographic protocol. Arbitrary inconsistent
answers at ≥k positions do not necessarily admit such a p.

`stateOfAvailable` binds the count state to an actual Finset cardinality.
`recoverable_polynomial_reconstruction` combines its isRecoverable predicate
with distinct nodes, authentic values and degree<k to recover the original
polynomial by interpolation. `mds_interpolate_authentic` additionally takes DecidableEq for the index type;
the ExistsUnique theorem uses classical decidability inside its proof.

If selected.card<k, `shortage_two_polynomials` supplies distinct polynomials
0 and the nodal polynomial, both of degree <k and agreeing at selected nodes.
This refutes universal uniqueness with too few points; it is not a statement
about a particular executable decoder. This theorem does not require distinct
nodes. Field size and a global system of n distinct nodes are not automatically
constructed from n=2k.

## Exact finite sampling space

`SamplingTrace n S := Fin S → Fin n`: the n^S ordered query sequences are
equiprobable, with independent coordinates and replacement; duplicates are allowed.
For fixed `available : Finset (Fin n)`, a successful trace has all coordinates
in that set. An explicit equivalence to functions `Fin S → available` proves
that the number of successful traces is |available|^S.

`samplingSuccessProbability` is the rational ratio of these cardinalities;
the proved formula is `(available.card/n)^S`. Its probability interpretation
requires n>0, supplied by RSBlockParams. The formulas are total even at n=0,
but this degenerate case does not describe a positive-size sampling block.
At S=0 the unique empty trace succeeds and the probability is 1.

For count-unrecoverable available.card<k and n=2k, the available fraction is
≤1/2, so all-query success probability is ≤(1/2)^S.
`maxDeceptionProbability` names this conservative ceiling; it is not claimed
to be an attained maximum for a fixed finite k. The ceiling strictly decreases
with S, while actual probability is only nonincreasing in general: an empty
available set, for example, gives zero for every S>0.

## Twenty queries and the saving limitation

The exact result is `(1/2)^20 = 1/1048576 < 1/1000000`, together with the
corresponding bound on actual samplingSuccessProbability when available.card<k.
The ceiling is independent of k,n. `light_client_verification_model` additionally
requires 20<n to conclude that query positions are fewer than all shard positions.
Without this premise, 20 queries need not beat downloading the whole block.
Duplicates do not provide 20 distinct shards. Query-position count does not
bound bytes, proof sizes, reconstruction work or network overhead.

## Scope

Availability is static; sampling is uniform, independent and nonadaptive.
The probability concerns all queries hitting available despite too few distinct
available code shards. It does not guarantee future serving, adaptive-server
behavior, or unbiased and uncorrelated network sampling. Responses must separately
be connected to authentic evaluations of one valid codeword. There is no KZG,
Eclipse protection, timeout model or forged-response security proof. Physical
quantum snapshots, a no-cloning bridge and hardware costs are outside scope.
Use for serialized classical data requires its own representation/code correspondence.

Polynomial proofs use Mathlib Lagrange interpolation and degree properties;
sampling proofs use an explicit finite equivalence, function cardinalities and
rational order. There are no direct Verification imports. Novelty is not assessed;
publication, hardware authorization and the Third Obligation are unchanged.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [mds_recovery_threshold](../../Verification/DataAvailabilitySamplingContract.lean#L40)
- [actual_set_recoverable_iff](../../Verification/DataAvailabilitySamplingContract.lean#L152)
- [recoverable_polynomial_reconstruction](../../Verification/DataAvailabilitySamplingContract.lean#L225)
- [unrecoverable_erasure_bound](../../Verification/DataAvailabilitySamplingContract.lean#L48)
- [mds_unique_of_card_le](../../Verification/DataAvailabilitySamplingContract.lean#L169)
- [mds_interpolate_authentic](../../Verification/DataAvailabilitySamplingContract.lean#L179)
- [mds_existsUnique_authentic](../../Verification/DataAvailabilitySamplingContract.lean#L190)
- [shortage_two_polynomials](../../Verification/DataAvailabilitySamplingContract.lean#L209)
- [successful_trace_count](../../Verification/DataAvailabilitySamplingContract.lean#L67)
- [all_trace_count](../../Verification/DataAvailabilitySamplingContract.lean#L72)
- [sampling_probability_formula](../../Verification/DataAvailabilitySamplingContract.lean#L80)
- [sampling_probability_bounds](../../Verification/DataAvailabilitySamplingContract.lean#L94)
- [sampling_probability_antitone](../../Verification/DataAvailabilitySamplingContract.lean#L101)
- [unrecoverable_fraction_bound](../../Verification/DataAvailabilitySamplingContract.lean#L108)
- [sampling_deception_decay](../../Verification/DataAvailabilitySamplingContract.lean#L117)
- [max_deception_strict_decay](../../Verification/DataAvailabilitySamplingContract.lean#L124)
- [sampling_security_exponential_bound](../../Verification/DataAvailabilitySamplingContract.lean#L128)
- [twenty_sample_security](../../Verification/DataAvailabilitySamplingContract.lean#L133)
- [ceiling_parameter_independent](../../Verification/DataAvailabilitySamplingContract.lean#L139)
- [light_client_verification_model](../../Verification/DataAvailabilitySamplingContract.lean#L156)
- [verification_suite](../../Verification/DataAvailabilitySamplingContract.lean#L261)
