/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.Quaternion
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.Ring

/-!
# Real quaternion conjugation and Euclidean isometry

Mathlib supplies the Hamilton algebra and unitary group. This module fixes their
coordinate interface and proves the action on pure three-vectors. No SU(2)
isomorphism, SO(3) surjectivity, covering theorem or physical implementation is claimed.
-/
namespace AlgebraQuaternionSpinor

noncomputable section

open scoped Quaternion

abbrev Quat := Quaternion ℝ

namespace Quat
abbrev mk (w x y z : ℝ) : Quat := ⟨w, x, y, z⟩
abbrev w (q : Quat) : ℝ := q.re
abbrev x (q : Quat) : ℝ := q.imI
abbrev y (q : Quat) : ℝ := q.imJ
abbrev z (q : Quat) : ℝ := q.imK
end Quat

abbrev conj (q : Quat) : Quat := star q
noncomputable def normSq (q : Quat) : ℝ := Quaternion.normSq q

theorem normSq_coordinates (q : Quat) :
    normSq q = q.w ^ 2 + q.x ^ 2 + q.y ^ 2 + q.z ^ 2 :=
  Quaternion.normSq_def' q

abbrev basisI : Quat := ⟨0, 1, 0, 0⟩
abbrev basisJ : Quat := ⟨0, 0, 1, 0⟩
abbrev basisK : Quat := ⟨0, 0, 0, 1⟩

theorem hamilton_relations :
    basisI * basisI = -1 ∧ basisJ * basisJ = -1 ∧ basisK * basisK = -1 ∧
      basisI * basisJ = basisK ∧ basisJ * basisI = -basisK ∧
      (basisI * basisJ) * basisK = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Quaternion.re_neg, Quaternion.imI_neg,
      Quaternion.imJ_neg, Quaternion.imK_neg] <;>
    norm_num [basisI, basisJ, basisK]

theorem quat_mul_assoc (a b c : Quat) : (a * b) * c = a * (b * c) := mul_assoc a b c

theorem quat_conj_mul (a b : Quat) : conj (a * b) = conj b * conj a := star_mul a b

theorem quat_norm_mul (a b : Quat) : normSq (a * b) = normSq a * normSq b :=
  Quaternion.normSq.map_mul a b

theorem normSq_conj (q : Quat) : normSq (conj q) = normSq q := Quaternion.normSq_star q

theorem quat_unit_inverse (q : Quat) (h : normSq q = 1) : q * conj q = 1 := by
  rw [conj, Quaternion.self_mul_star, ← normSq, h, Quaternion.coe_one]

theorem quat_unit_inverse_left (q : Quat) (h : normSq q = 1) : conj q * q = 1 := by
  rw [conj, Quaternion.star_mul_self, ← normSq, h, Quaternion.coe_one]

abbrev UnitQuat := unitary Quat

theorem mem_unitQuat_iff (q : Quat) : q ∈ unitary Quat ↔ normSq q = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun p : Quat => p.re) h.2
    simpa [Quaternion.normSq_def, normSq] using h'
  · intro h
    exact ⟨quat_unit_inverse_left q h, quat_unit_inverse q h⟩

noncomputable def unitOfNormSq (q : Quat) (h : normSq q = 1) : UnitQuat :=
  ⟨q, (mem_unitQuat_iff q).mpr h⟩

theorem unit_normSq (q : UnitQuat) : normSq (q : Quat) = 1 :=
  (mem_unitQuat_iff q).mp q.property

theorem unit_inv_conj (q : UnitQuat) : ((q⁻¹ : UnitQuat) : Quat) = conj (q : Quat) := rfl

/-- Coordinate compatibility with the original triple specification. -/
abbrev pureVec (v : ℝ × ℝ × ℝ) : Quat := ⟨0, v.1, v.2.1, v.2.2⟩

/-- Purity holds even without unit norm. -/
theorem conjugation_pure (q p : Quat) (hp : p.re = 0) : (q * p * conj q).re = 0 := by
  simp [conj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, hp]
  ring

theorem conjugation_normSq (q p : Quat) (hq : normSq q = 1) :
    normSq (q * p * conj q) = normSq p := by
  rw [quat_norm_mul, quat_norm_mul, normSq_conj, hq, one_mul, mul_one]

theorem quat_rotation_isometry (q : Quat) (hq : normSq q = 1) (v : ℝ × ℝ × ℝ) :
    (q * pureVec v * conj q).w = 0 ∧ normSq (q * pureVec v * conj q) = normSq (pureVec v) :=
  ⟨conjugation_pure q _ rfl, conjugation_normSq q _ hq⟩

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)
noncomputable def embed (v : Vec3) : Quat := ⟨0, v 0, v 1, v 2⟩
noncomputable def coords (q : Quat) : Vec3 := !₂[q.imI, q.imJ, q.imK]

@[simp] theorem coords_embed (v : Vec3) : coords (embed v) = v := by
  ext i
  fin_cases i <;> rfl

theorem embed_coords (p : Quat) (hp : p.re = 0) : embed (coords p) = p := by
  ext <;> simp [embed, coords, hp]

theorem embed_injective : Function.Injective embed := by
  intro u v h
  simpa using congrArg coords h

theorem embed_add (u v : Vec3) : embed (u + v) = embed u + embed v := by
  apply QuaternionAlgebra.ext
  · change (0 : ℝ) = 0 + 0; ring
  · rfl
  · rfl
  · rfl

theorem embed_smul (r : ℝ) (v : Vec3) : embed (r • v) = r • embed v := by
  apply QuaternionAlgebra.ext
  · change (0 : ℝ) = r * 0; ring
  · rfl
  · rfl
  · rfl

theorem embed_norm (v : Vec3) : ‖embed v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, Quaternion.inner_self, Quaternion.normSq_def',
    EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp [embed, Real.norm_eq_abs, sq_abs]

noncomputable def rotate (q : UnitQuat) (v : Vec3) : Vec3 :=
  coords ((q : Quat) * embed v * conj (q : Quat))

theorem embed_rotate (q : UnitQuat) (v : Vec3) :
    embed (rotate q v) = (q : Quat) * embed v * conj (q : Quat) :=
  embed_coords _ (conjugation_pure _ _ rfl)

theorem rotate_add (q : UnitQuat) (u v : Vec3) : rotate q (u + v) = rotate q u + rotate q v := by
  apply embed_injective
  simp only [embed_rotate, embed_add, mul_add, add_mul]

theorem rotate_smul (q : UnitQuat) (r : ℝ) (v : Vec3) : rotate q (r • v) = r • rotate q v := by
  apply embed_injective
  simp only [embed_rotate, embed_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

theorem rotate_norm (q : UnitQuat) (v : Vec3) : ‖rotate q v‖ = ‖v‖ := by
  rw [← embed_norm, ← embed_norm v, embed_rotate]
  rw [norm_eq_sqrt_real_inner, Quaternion.inner_self,
    norm_eq_sqrt_real_inner (embed v), Quaternion.inner_self]
  congr 1
  exact conjugation_normSq _ _ (unit_normSq q)

theorem rotate_one (v : Vec3) : rotate 1 v = v := by
  apply embed_injective
  simp [embed_rotate, conj]

theorem rotate_mul (q r : UnitQuat) (v : Vec3) : rotate (q * r) v = rotate q (rotate r v) := by
  apply embed_injective
  simp only [embed_rotate, Submonoid.coe_mul, quat_conj_mul, mul_assoc]

theorem rotate_inverse (q : UnitQuat) (v : Vec3) : rotate q⁻¹ (rotate q v) = v := by
  rw [← rotate_mul, inv_mul_cancel, rotate_one]

theorem rotate_dist (q : UnitQuat) (u v : Vec3) : dist (rotate q u) (rotate q v) = dist u v := by
  have hn : rotate q (-v) = -rotate q v := by simpa using rotate_smul q (-1) v
  rw [dist_eq_norm, dist_eq_norm, ← rotate_norm q (u - v)]
  congr 1
  simp [sub_eq_add_neg, rotate_add, hn]

/-- The two opposite quaternions always induce the same sandwich action. -/
theorem opposite_same_action (q p : Quat) : (-q) * p * conj (-q) = q * p * conj q := by
  simp [conj]

/-- Unit norm is essential for the sandwich with conjugate, as opposed to inverse. -/
theorem nonunit_counterexample :
    normSq ((2 : Quat) * basisI * conj (2 : Quat)) ≠ normSq basisI := by
  rw [quat_norm_mul, quat_norm_mul, normSq_conj]
  have h2 : normSq (2 : Quat) = 4 := by
    rw [normSq_coordinates]
    change (2 : ℝ)^2 + 0^2 + 0^2 + 0^2 = 4
    norm_num
  have hi : normSq basisI = 1 := by
    rw [normSq_coordinates]
    change (0 : ℝ)^2 + 1^2 + 0^2 + 0^2 = 1
    norm_num
  rw [h2, hi]
  norm_num

structure QuaternionSpinorSuite : Prop where
  associative : ∀ a b c : Quat, (a * b) * c = a * (b * c)
  conjugate_mul : ∀ a b : Quat, conj (a * b) = conj b * conj a
  multiplicative_norm : ∀ a b : Quat, normSq (a * b) = normSq a * normSq b
  unit_inverse : ∀ q : Quat, normSq q = 1 → q * conj q = 1 ∧ conj q * q = 1
  pure_isometry : ∀ (q : Quat), normSq q = 1 → ∀ v : ℝ × ℝ × ℝ,
    (q * pureVec v * conj q).w = 0 ∧ normSq (q * pureVec v * conj q) = normSq (pureVec v)
  euclidean_isometry : ∀ (q : UnitQuat) (u v : Vec3), dist (rotate q u) (rotate q v) = dist u v
  action_composition : ∀ (q r : UnitQuat) (v : Vec3), rotate (q * r) v = rotate q (rotate r v)
  inverse_action : ∀ (q : UnitQuat) (v : Vec3), rotate q⁻¹ (rotate q v) = v

theorem verification_suite : QuaternionSpinorSuite := {
  associative := quat_mul_assoc
  conjugate_mul := quat_conj_mul
  multiplicative_norm := quat_norm_mul
  unit_inverse := fun q h => ⟨quat_unit_inverse q h, quat_unit_inverse_left q h⟩
  pure_isometry := quat_rotation_isometry
  euclidean_isometry := rotate_dist
  action_composition := rotate_mul
  inverse_action := rotate_inverse
}

end

end AlgebraQuaternionSpinor
