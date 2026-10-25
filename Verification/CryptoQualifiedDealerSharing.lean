/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoFeldmanVSSGroup

/-! Algebraic aggregation after an agreed qualified-dealer set has been fixed.
Agreement on this set and reliable delivery are assumptions, not protocol proofs. -/
noncomputable section
open Polynomial CryptoFeldmanVSSGroup CryptoShamirSecretSharingGroup
open scoped BigOperators
namespace CryptoQualifiedDealerSharing
variable {K B D : Type*} [Field K] [AddCommGroup B] [Module K B]

def aggregatePoly (Q : Finset D) (p : D → K[X]) : K[X] := ∑ d ∈ Q, p d

theorem aggregate_degree (Q : Finset D) (p : D → K[X]) {n : ℕ} (hn : 0 < n)
    (hp : ∀ d ∈ Q, (p d).natDegree < n) : (aggregatePoly Q p).natDegree < n := by
  classical
  unfold aggregatePoly
  induction Q using Finset.induction_on with
  | empty => simpa using hn
  | @insert d Q hd ih =>
    rw [Finset.sum_insert hd]
    exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (hp d (by simp))
      (ih (fun j hj => hp j (by simp [hj]))))

theorem aggregate_eval (Q : Finset D) (p : D → K[X]) (x : K) :
    (aggregatePoly Q p).eval x = ∑ d ∈ Q, (p d).eval x := by
  simp [aggregatePoly, eval_finsetSum]

theorem aggregate_commitments (G : B) (Q : Finset D) (p : D → K[X]) (j : ℕ) :
    commitments G (aggregatePoly Q p) j = ∑ d ∈ Q, commitments G (p d) j := by
  simp [commitments, aggregatePoly, Finset.sum_smul]

theorem checked_shares_sum (G : B) (hG : Function.Injective (fun y : K => y • G))
    (Q : Finset D) (p : D → K[X]) (n : ℕ) (hp : ∀ d ∈ Q, (p d).natDegree < n)
    (x : K) (ys : D → K)
    (hv : ∀ d ∈ Q, Verify G n (commitments G (p d)) x (ys d)) :
    ∑ d ∈ Q, ys d = (aggregatePoly Q p).eval x := by
  rw [aggregate_eval]
  apply Finset.sum_congr rfl
  intro d hd
  exact (verify_iff_evaluation G hG (p d) (hp d hd) x (ys d)).mp (hv d hd)

theorem receiver_consistency (G : B) (hG : Function.Injective (fun y : K => y • G))
    (Q : Finset D) (p : D → K[X]) (n : ℕ) (hp : ∀ d ∈ Q, (p d).natDegree < n)
    (x : K) (ys zs : D → K)
    (hy : ∀ d ∈ Q, Verify G n (commitments G (p d)) x (ys d))
    (hz : ∀ d ∈ Q, Verify G n (commitments G (p d)) x (zs d)) :
    ∑ d ∈ Q, ys d = ∑ d ∈ Q, zs d := by
  rw [checked_shares_sum G hG Q p n hp x ys hy, checked_shares_sum G hG Q p n hp x zs hz]

theorem qualified_reconstruction {ι : Type*} [DecidableEq ι]
    (Q : Finset D) (p : D → K[X]) {n : ℕ} (hn : 0 < n)
    (hp : ∀ d ∈ Q, (p d).natDegree < n) (ids : ι → K) (hi : Function.Injective ids)
    (I : Finset ι) (hI : n ≤ I.card) :
    ∑ i ∈ I, lagrange_coeff ids I i * (∑ d ∈ Q, (p d).eval (ids i)) =
      ∑ d ∈ Q, (p d).eval 0 := by
  simp_rw [← aggregate_eval]
  exact field_lagrange_bridge ids hi I (aggregatePoly Q p)
    (lt_of_lt_of_le (aggregate_degree Q p hn hp) hI)

/-- Changing the qualified set can change the secret, even with valid individual dealers. -/
theorem inserted_dealer_changes_secret [DecidableEq D] (Q : Finset D) (p : D → K[X]) (d : D)
    (hd : d ∉ Q) (hs : (p d).eval 0 ≠ 0) :
    (aggregatePoly (insert d Q) p).eval 0 ≠ (aggregatePoly Q p).eval 0 := by
  simp only [aggregate_eval, Finset.sum_insert hd]
  intro h
  exact hs (add_right_cancel (h.trans (zero_add _).symm))

/-- Aggregate equality alone cannot validate each dealer's contribution. -/
theorem cancelling_errors (a b e : K) : (a + e) + (b - e) = a + b := by ring

structure CryptoQualifiedDealerSharingSuite : Prop where
  degree : ∀ (K D : Type) [Field K] [DecidableEq D] (Q : Finset D) (p : D → K[X])
    (n : ℕ), 0 < n → (∀ d ∈ Q, (p d).natDegree < n) → (aggregatePoly Q p).natDegree < n
  reconstruction : ∀ (K D ι : Type) [Field K] [DecidableEq D] [DecidableEq ι]
    (Q : Finset D) (p : D → K[X]) (n : ℕ), 0 < n →
    (∀ d ∈ Q, (p d).natDegree < n) → ∀ (ids : ι → K), Function.Injective ids →
    ∀ (I : Finset ι), n ≤ I.card →
    ∑ i ∈ I, lagrange_coeff ids I i * (∑ d ∈ Q, (p d).eval (ids i)) = ∑ d ∈ Q, (p d).eval 0

theorem verification_suite : CryptoQualifiedDealerSharingSuite where
  degree := fun _ _ _ _ Q p _ hn hp => aggregate_degree Q p hn hp
  reconstruction := fun _ _ _ _ _ _ Q p _ hn hp ids hi I hI =>
    qualified_reconstruction Q p hn hp ids hi I hI
end CryptoQualifiedDealerSharing
