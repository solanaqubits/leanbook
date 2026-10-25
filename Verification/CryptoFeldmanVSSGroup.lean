/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoShamirSecretSharingGroup
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Arbitrary-degree Feldman share consistency

Coefficient commitments live in an additive module over a field. The prime-field
specialization uses the existing cyclic setup; no concrete elliptic curve is
implemented. One fixed public commitment vector is required throughout recovery.
No reliable broadcast, complaint protocol, dealer honesty or secrecy is asserted.
-/

noncomputable section
open scoped BigOperators
open Polynomial CryptoShamirSecretSharingGroup

namespace CryptoFeldmanVSSGroup

section Algebra
variable {K B : Type*} [Field K] [AddCommGroup B] [Module K B]

def commitments (G : B) (p : K[X]) (j : ℕ) : B := p.coeff j • G

def evaluateCommitments (n : ℕ) (C : ℕ → B) (x : K) : B :=
  ∑ j ∈ Finset.range n, (x ^ j) • C j

def Verify (G : B) (n : ℕ) (C : ℕ → B) (x y : K) : Prop :=
  y • G = evaluateCommitments n C x

theorem evaluation_commutes (G : B) (p : K[X]) {n : ℕ}
    (hn : p.natDegree < n) (x : K) :
    evaluateCommitments n (commitments G p) x = p.eval x • G := by
  rw [Polynomial.eval_eq_sum_range' hn]
  simp only [evaluateCommitments, commitments, Finset.sum_smul, smul_smul]
  simp_rw [mul_comm]

theorem honest_completeness (G : B) (p : K[X]) {n : ℕ}
    (hn : p.natDegree < n) (x : K) :
    Verify G n (commitments G p) x (p.eval x) := by
  rw [Verify, evaluation_commutes G p hn]

theorem verify_iff_evaluation (G : B) (hG : Function.Injective (fun y : K => y • G))
    (p : K[X]) {n : ℕ} (hn : p.natDegree < n) (x y : K) :
    Verify G n (commitments G p) x y ↔ y = p.eval x := by
  rw [Verify, evaluation_commutes G p hn]
  exact hG.eq_iff

theorem accepted_share_unique (G : B) (hG : Function.Injective (fun y : K => y • G))
    (n : ℕ) (C : ℕ → B) (x y z : K)
    (hy : Verify G n C x y) (hz : Verify G n C x z) : y = z :=
  hG (hy.trans hz.symm)

theorem shifted_share_rejected (G : B)
    (hG : Function.Injective (fun y : K => y • G))
    (p : K[X]) {n : ℕ} (hn : p.natDegree < n) (x d : K) (hd : d ≠ 0) :
    ¬ Verify G n (commitments G p) x (p.eval x + d) := by
  rw [verify_iff_evaluation G hG p hn]
  simpa using hd

theorem committed_polynomial_unique (G : B)
    (hG : Function.Injective (fun y : K => y • G)) (p q : K[X]) {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n)
    (h : ∀ j < n, commitments G p j = commitments G q j) : p = q := by
  apply Polynomial.ext
  intro j
  by_cases hj : j < n
  · exact hG (h j hj)
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp (Nat.le_of_not_gt hj)),
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hq (Nat.le_of_not_gt hj))]

theorem verified_reconstruction {ι : Type*} [DecidableEq ι]
    (G : B) (hG : Function.Injective (fun y : K => y • G))
    (p : K[X]) {n : ℕ} (hn : p.natDegree < n)
    (ids : ι → K) (hids : Function.Injective ids) (I : Finset ι)
    (hI : n ≤ I.card) (shares : ι → K)
    (hv : ∀ i ∈ I, Verify G n (commitments G p) (ids i) (shares i)) :
    ∑ i ∈ I, lagrange_coeff ids I i * shares i = p.eval 0 := by
  calc
    _ = ∑ i ∈ I, lagrange_coeff ids I i * p.eval (ids i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(verify_iff_evaluation G hG p hn _ _).mp (hv i hi)]
    _ = _ := field_lagrange_bridge ids hids I p (lt_of_lt_of_le hn hI)

theorem commitments_add (G : B) (p q : K[X]) (j : ℕ) :
    commitments G (p + q) j = commitments G p j + commitments G q j := by
  simp [commitments, add_smul]

theorem combine_verified (G : B) (n : ℕ) (C D : ℕ → B) (x y z : K)
    (hy : Verify G n C x y) (hz : Verify G n D x z) :
    Verify G n (fun j => C j + D j) x (y + z) := by
  simp only [Verify, add_smul, evaluateCommitments, smul_add, Finset.sum_add_distrib] at *
  rw [hy, hz]

/-- The public constant commitment is a secret-dependent group element. -/
theorem different_secrets_different_commitments (G : B)
    (hG : Function.Injective (fun y : K => y • G)) (p q : K[X])
    (h : p.eval 0 ≠ q.eval 0) : commitments G p 0 ≠ commitments G q 0 := by
  intro he
  apply h
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using hG he

/-- Without an injective generator action every scalar passes the zero commitments. -/
theorem zero_generator_accepts (n : ℕ) (x y : K) :
    Verify (0 : B) n (fun _ => 0) x y := by
  simp [Verify, evaluateCommitments]

end Algebra

section PrimeField
variable {q : ℕ} [Fact (Nat.Prime q)]
variable {B : Type} [AddCommGroup B] [Module (ZMod q) B]
open CryptoSchnorrMultiSignaturesMuSigGroup

theorem prime_field_soundness (S : CyclicSetup q B) (p : (ZMod q)[X])
    {n : ℕ} (hn : p.natDegree < n) (x y : ZMod q) :
    Verify S.generator n (commitments S.generator p) x y ↔ y = p.eval x :=
  verify_iff_evaluation S.generator (scalar_action_injective S) p hn x y

/-- Even a malicious dealer's fixed group commitments determine one polynomial.
This is mathematical existence via surjectivity, not efficient discrete-log recovery. -/
theorem arbitrary_commitments_determine_polynomial (S : CyclicSetup q B)
    (n : ℕ) (hn : 0 < n) (C : ℕ → B) :
    ∃! p : (ZMod q)[X], p.natDegree < n ∧
      ∀ j < n, commitments S.generator p j = C j := by
  classical
  let a : Fin n → ZMod q := fun i => (S.generator_bijective.2 (C i)).choose
  let p := Polynomial.ofFn n a
  have hp : p.natDegree < n := Polynomial.ofFn_natDegree_lt hn a
  have hc : ∀ j < n, commitments S.generator p j = C j := by
    intro j hj
    simp only [commitments, p, Polynomial.ofFn_coeff_eq_val_of_lt a hj]
    exact (S.generator_bijective.2 (C j)).choose_spec
  refine ⟨p, ⟨hp, hc⟩, ?_⟩
  intro r hr
  exact committed_polynomial_unique S.generator (scalar_action_injective S)
    r p hr.1 hp (fun j hj => (hr.2 j hj).trans (hc j hj).symm)

theorem arbitrary_verified_family_consistent (S : CyclicSetup q B)
    (n : ℕ) (hn : 0 < n) (C : ℕ → B) :
    ∃ p : (ZMod q)[X], p.natDegree < n ∧ ∀ x y,
      Verify S.generator n C x y ↔ y = p.eval x := by
  obtain ⟨p, hp, _⟩ := arbitrary_commitments_determine_polynomial S n hn C
  refine ⟨p, hp.1, ?_⟩
  intro x y
  have he : evaluateCommitments n (commitments S.generator p) x =
      evaluateCommitments n C x := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hp.2 j (Finset.mem_range.mp hj)]
  rw [Verify, ← he]
  exact prime_field_soundness S p hp.1 x y

end PrimeField

structure CryptoFeldmanVSSGroupSuite : Prop where
  consistency : ∀ (q : ℕ) [Fact (Nat.Prime q)] (B : Type) [AddCommGroup B]
    [Module (ZMod q) B] (S : CryptoSchnorrMultiSignaturesMuSigGroup.CyclicSetup q B)
    (p : (ZMod q)[X]) (n : ℕ), p.natDegree < n → ∀ x y,
    Verify S.generator n (commitments S.generator p) x y ↔ y = p.eval x
  uniqueness : ∀ (K B : Type) [Field K] [AddCommGroup B] [Module K B]
    (G : B), Function.Injective (fun y : K => y • G) → ∀ (p q : K[X]) (n : ℕ),
    p.natDegree < n → q.natDegree < n →
    (∀ j < n, commitments G p j = commitments G q j) → p = q
  reconstruction : ∀ (K B ι : Type) [Field K] [AddCommGroup B] [Module K B]
    [DecidableEq ι] (G : B), Function.Injective (fun y : K => y • G) →
    ∀ (p : K[X]) (n : ℕ), p.natDegree < n → ∀ (ids : ι → K),
    Function.Injective ids → ∀ (I : Finset ι), n ≤ I.card → ∀ (shares : ι → K),
    (∀ i ∈ I, Verify G n (commitments G p) (ids i) (shares i)) →
    ∑ i ∈ I, lagrange_coeff ids I i * shares i = p.eval 0
  arbitrary_family : ∀ (q : ℕ) [Fact (Nat.Prime q)] (B : Type) [AddCommGroup B]
    [Module (ZMod q) B] (S : CryptoSchnorrMultiSignaturesMuSigGroup.CyclicSetup q B)
    (n : ℕ), 0 < n → ∀ C, ∃ p : (ZMod q)[X], p.natDegree < n ∧ ∀ x y,
    Verify S.generator n C x y ↔ y = p.eval x

theorem verification_suite : CryptoFeldmanVSSGroupSuite where
  consistency := fun _ _ _ _ _ S p _ hn => prime_field_soundness S p hn
  uniqueness := fun _ _ _ _ _ G hG p q _ hp hq => committed_polynomial_unique G hG p q hp hq
  reconstruction := fun _ _ _ _ _ _ _ G hG p _ hn ids hids I hI shares =>
    verified_reconstruction G hG p hn ids hids I hI shares
  arbitrary_family := fun _ _ _ _ _ S n hn C => arbitrary_verified_family_consistent S n hn C

end CryptoFeldmanVSSGroup
