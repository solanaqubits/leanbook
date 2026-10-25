/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoFeldmanVSSGroup

/-! Recovery at an arbitrary coordinate from a threshold set of verified shares.
This is an algebraic repair procedure, not a private communication protocol. -/
noncomputable section
open Polynomial CryptoShamirSecretSharingGroup
open scoped BigOperators
namespace CryptoShamirShareRepair
variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

def weight (ids : ι → K) (I : Finset ι) (z : K) (i : ι) : K :=
  ∏ j ∈ I.erase i, (z - ids j) * (ids i - ids j)⁻¹

def repair (ids : ι → K) (I : Finset ι) (ys : ι → K) (z : K) : K :=
  ∑ i ∈ I, weight ids I z i * ys i

theorem repair_evaluations (ids : ι → K) (hi : Function.Injective ids)
    (I : Finset ι) (p : K[X]) (hp : p.natDegree < I.card) (z : K) :
    repair ids I (fun i => p.eval (ids i)) z = p.eval z := by
  have hd : p.degree < (I.card : WithBot ℕ) :=
    lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hp)
  have he := congrArg (Polynomial.eval z) (Lagrange.eq_interpolate (hi.injOn (s := ↑I)) hd)
  simpa [repair, weight, Lagrange.interpolate_apply, Lagrange.basis,
    Lagrange.basisDivisor, eval_finsetSum, eval_prod, mul_comm] using he.symm

theorem repair_verified {B : Type*} [AddCommGroup B] [Module K B]
    (G : B) (hG : Function.Injective (fun y : K => y • G)) (p : K[X])
    {n : ℕ} (hp : p.natDegree < n) (ids : ι → K) (hi : Function.Injective ids)
    (I : Finset ι) (hI : n ≤ I.card) (ys : ι → K)
    (hv : ∀ i ∈ I, CryptoFeldmanVSSGroup.Verify G n
      (CryptoFeldmanVSSGroup.commitments G p) (ids i) (ys i)) (z : K) :
    repair ids I ys z = p.eval z := by
  rw [← repair_evaluations ids hi I p (lt_of_lt_of_le hp hI) z]
  apply Finset.sum_congr rfl
  intro i hm
  rw [(CryptoFeldmanVSSGroup.verify_iff_evaluation G hG p hp (ids i) (ys i)).mp (hv i hm)]

theorem repaired_share_verifies {B : Type*} [AddCommGroup B] [Module K B]
    (G : B) (p : K[X]) {n : ℕ} (hp : p.natDegree < n)
    (ids : ι → K) (hi : Function.Injective ids) (I : Finset ι) (hI : n ≤ I.card) (z : K) :
    CryptoFeldmanVSSGroup.Verify G n (CryptoFeldmanVSSGroup.commitments G p) z
      (repair ids I (fun i => p.eval (ids i)) z) := by
  rw [repair_evaluations ids hi I p (lt_of_lt_of_le hp hI)]
  exact CryptoFeldmanVSSGroup.honest_completeness G p hp z

/-- Any two threshold sets recover the same destination share. -/
theorem repair_quorum_independent (ids : ι → K) (hi : Function.Injective ids)
    (I J : Finset ι) (p : K[X]) (hI : p.natDegree < I.card)
    (hJ : p.natDegree < J.card) (z : K) :
    repair ids I (fun i => p.eval (ids i)) z = repair ids J (fun i => p.eval (ids i)) z := by
  rw [repair_evaluations ids hi I p hI, repair_evaluations ids hi J p hJ]

/-- A single erroneous contribution is not masked when its interpolation weight is nonzero. -/
theorem contribution_error (w y e : K) (hw : w ≠ 0) (he : e ≠ 0) :
    w * (y + e) ≠ w * y := by
  intro h
  apply he
  have := (mul_left_cancel₀ hw h)
  exact add_left_cancel (this.trans (add_zero y).symm)

structure CryptoShamirShareRepairSuite : Prop where
  recovery : ∀ (K ι : Type) [Field K] [DecidableEq ι] (ids : ι → K),
    Function.Injective ids → ∀ (I : Finset ι) (p : K[X]), p.natDegree < I.card →
    ∀ z, repair ids I (fun i => p.eval (ids i)) z = p.eval z
  agreement : ∀ (K ι : Type) [Field K] [DecidableEq ι] (ids : ι → K),
    Function.Injective ids → ∀ (I J : Finset ι) (p : K[X]),
    p.natDegree < I.card → p.natDegree < J.card → ∀ z,
    repair ids I (fun i => p.eval (ids i)) z = repair ids J (fun i => p.eval (ids i)) z

theorem verification_suite : CryptoShamirShareRepairSuite where
  recovery := fun _ _ _ _ ids hi I p hp => repair_evaluations ids hi I p hp
  agreement := fun _ _ _ _ ids hi I J p hI hJ => repair_quorum_independent ids hi I J p hI hJ
end CryptoShamirShareRepair
