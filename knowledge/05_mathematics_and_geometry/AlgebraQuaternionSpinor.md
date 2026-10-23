---
id: AlgebraQuaternionSpinor
language: en
section: quantum-physics
source: Verification/AlgebraQuaternionSpinor.lean
novelty: not-assessed
status: reviewed
source_sha256: e4d4087fcb064019253fc8fb1bd08bb08fb14738d01069d189cfa34c13b8d852
---

# Real quaternions and Euclidean conjugation isometry

[Section](../quantum-physics/README.md) · [Lean](../../Verification/AlgebraQuaternionSpinor.lean)

Stage ε263, batch `quantum-physics/quaternion-spinor`. The module uses
Mathlib's `Quaternion ℝ` and `unitary`; it does not postulate a new
quaternion algebra.

## Exact result

`normSq q = w² + x² + y² + z²`. The module establishes Hamilton relations
for `basisI`, `basisJ`, `basisK`, associativity, reversal of multiplication
under conjugation, and multiplicativity of the squared norm. The condition
`normSq q = 1` is equivalent to membership in `unitary Quat`; under this
condition `conj q` is both a left and a right inverse. The `UnitQuat` group
is inherited from Mathlib.

For a pure quaternion `p` (`p.re = 0`), `q * p * conj q` is pure for every
`q`. If `q` has unit norm, it also preserves `normSq p`. The `pureVec`
interface expresses this result for a triple of real coordinates.

`Vec3 := EuclideanSpace ℝ (Fin 3)` uses the Euclidean norm. The maps
`embed` and `coords` are mutually inverse on pure quaternions; `embed` is
injective, linear and norm preserving. For `q : UnitQuat`, `rotate q` is
defined by conjugating the embedded vector. The module proves additivity,
real homogeneity, preservation of norm and distance, the identity action,
and `rotate (q * r) v = rotate q (rotate r v)`.
The action of `q⁻¹` reverses the action of `q`.

## Assumptions and limits

Preservation of purity does not require unit norm; preservation of length
by this conjugation does. `nonunit_counterexample` exhibits failure of
squared-norm preservation for `q = 2` and `p = basisI`. Opposite `q` and
`-q` induce the same action; this alone does not classify the kernel.

The name Spinor does not introduce a physical spinor or a separate Spin
group. An SU(2) isomorphism, an SO(3) correspondence, surjectivity onto
rotations, determinant +1, a double covering and topological properties
are not proved. No physical implementation or hardware qualification is
asserted.

## Dependencies and reuse

There are no direct `Verification` imports. The module imports
`Mathlib.Analysis.Quaternion`, `Mathlib.Algebra.Star.Unitary` and
`Mathlib.Tactic.Ring`. The contract provides a coordinate interface and
a basis for further formalization of geometric actions. Novelty has not
been assessed; the underlying Hamilton algebra is already supplied by Mathlib.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [hamilton_relations](../../Verification/AlgebraQuaternionSpinor.lean#L44)
- [mem_unitQuat_iff](../../Verification/AlgebraQuaternionSpinor.lean#L71)
- [quat_rotation_isometry](../../Verification/AlgebraQuaternionSpinor.lean#L100)
- [embed_norm](../../Verification/AlgebraQuaternionSpinor.lean#L133)
- [rotate_add](../../Verification/AlgebraQuaternionSpinor.lean#L145)
- [rotate_smul](../../Verification/AlgebraQuaternionSpinor.lean#L149)
- [rotate_norm](../../Verification/AlgebraQuaternionSpinor.lean#L153)
- [rotate_dist](../../Verification/AlgebraQuaternionSpinor.lean#L171)
- [rotate_mul](../../Verification/AlgebraQuaternionSpinor.lean#L164)
- [rotate_inverse](../../Verification/AlgebraQuaternionSpinor.lean#L168)
- [opposite_same_action](../../Verification/AlgebraQuaternionSpinor.lean#L178)
- [nonunit_counterexample](../../Verification/AlgebraQuaternionSpinor.lean#L182)
- [verification_suite](../../Verification/AlgebraQuaternionSpinor.lean#L207)
