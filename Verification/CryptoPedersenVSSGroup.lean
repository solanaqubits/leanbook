/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoFeldmanVSSGroup
import Verification.CryptoPedersenHomomorphicSum

/-! Polynomial Pedersen share equations and the joint law of public coefficient
commitments. The hiding result samples every blinding coefficient independently
and uniformly. It does not include private share observations or active security. -/
noncomputable section
open scoped BigOperators
open Polynomial CryptoPedersenHomomorphicSum CryptoShamirSecretSharingGroup

namespace CryptoPedersenVSSGroup

variable {q : ℕ} [Fact q.Prime]
variable {B : Type} [Fintype B] [AddCommGroup B] [Module (ZMod q) B]

def commitments (S : CryptoPedersenHomomorphicSum.Setup q B)
    (p r : (ZMod q)[X]) (j : ℕ) : B := commit S (p.coeff j) (r.coeff j)

def Verify (S : CryptoPedersenHomomorphicSum.Setup q B)
    (n : ℕ) (C : ℕ → B) (x y z : ZMod q) : Prop :=
  commit S y z = CryptoFeldmanVSSGroup.evaluateCommitments n C x

theorem evaluation_commutes (S : CryptoPedersenHomomorphicSum.Setup q B)
    (p r : (ZMod q)[X]) {n : ℕ} (hp : p.natDegree < n) (hr : r.natDegree < n)
    (x : ZMod q) :
    CryptoFeldmanVSSGroup.evaluateCommitments n (commitments S p r) x =
      commit S (p.eval x) (r.eval x) := by
  simp only [CryptoFeldmanVSSGroup.evaluateCommitments, commitments, commit,
    smul_add, Finset.sum_add_distrib]
  change CryptoFeldmanVSSGroup.evaluateCommitments n
      (CryptoFeldmanVSSGroup.commitments S.g p) x +
    CryptoFeldmanVSSGroup.evaluateCommitments n
      (CryptoFeldmanVSSGroup.commitments S.h r) x = _
  rw [CryptoFeldmanVSSGroup.evaluation_commutes S.g p hp,
    CryptoFeldmanVSSGroup.evaluation_commutes S.h r hr]

theorem honest_completeness (S : CryptoPedersenHomomorphicSum.Setup q B)
    (p r : (ZMod q)[X]) {n : ℕ} (hp : p.natDegree < n) (hr : r.natDegree < n)
    (x : ZMod q) : Verify S n (commitments S p r) x (p.eval x) (r.eval x) := by
  rw [Verify, evaluation_commutes S p r hp hr]

/-- With the blinding evaluation fixed, an accepted message is unique. -/
theorem fixed_blinding_soundness (S : CryptoPedersenHomomorphicSum.Setup q B)
    (p r : (ZMod q)[X]) {n : ℕ} (hp : p.natDegree < n) (hr : r.natDegree < n)
    (x y : ZMod q) :
    Verify S n (commitments S p r) x y (r.eval x) ↔ y = p.eval x := by
  rw [Verify, evaluation_commutes S p r hp hr]
  simp only [commit, add_left_inj]
  exact (nonzero_generator_bijective S S.g_ne_zero).1.eq_iff

/-- Two accepted openings with different messages extract a generator relation. -/
theorem conflicting_shares_extract_relation (S : CryptoPedersenHomomorphicSum.Setup q B)
    (n : ℕ) (C : ℕ → B) (x y z y' z' : ZMod q)
    (h : Verify S n C x y z) (h' : Verify S n C x y' z') (hy : y ≠ y') :
    z ≠ z' ∧ S.h = ((y - y') * (z' - z)⁻¹) • S.g :=
  dlog_extraction_from_collision S (h.trans h'.symm) hy

def coefficientLaw (S : CryptoPedersenHomomorphicSum.Setup q B)
    {n : ℕ} (m : Fin n → ZMod q) : PMF (Fin n → B) :=
  (PMF.uniformOfFintype (Fin n → ZMod q)).map (fun r i => commit S (m i) (r i))

/-- The entire coefficient vector, not only its marginals, is uniformly distributed. -/
theorem coefficient_joint_uniform (S : CryptoPedersenHomomorphicSum.Setup q B)
    {n : ℕ} (m : Fin n → ZMod q) :
    coefficientLaw S m = PMF.uniformOfFintype (Fin n → B) := by
  exact CryptoPedersenHomomorphicSum.map_uniform_equiv
    (Equiv.piCongrRight fun i => commitEquiv S (m i))

theorem coefficient_joint_hiding (S : CryptoPedersenHomomorphicSum.Setup q B)
    {n : ℕ} (m m' : Fin n → ZMod q) : coefficientLaw S m = coefficientLaw S m' := by
  rw [coefficient_joint_uniform, coefficient_joint_uniform]

theorem verified_reconstruction_commitment {ι : Type} [DecidableEq ι]
    (S : CryptoPedersenHomomorphicSum.Setup q B) (p r : (ZMod q)[X])
    {n : ℕ} (hp : p.natDegree < n) (hr : r.natDegree < n)
    (ids : ι → ZMod q) (hi : Function.Injective ids) (I : Finset ι) (hI : n ≤ I.card)
    (ys zs : ι → ZMod q)
    (hv : ∀ i ∈ I, Verify S n (commitments S p r) (ids i) (ys i) (zs i)) :
    commit S (∑ i ∈ I, lagrange_coeff ids I i * ys i)
      (∑ i ∈ I, lagrange_coeff ids I i * zs i) = commit S (p.eval 0) (r.eval 0) := by
  rw [← commit_linear_combination S I]
  calc
    aggregate S I (lagrange_coeff ids I) ys zs =
        aggregate S I (lagrange_coeff ids I) (fun i => p.eval (ids i))
          (fun i => r.eval (ids i)) := by
      apply Finset.sum_congr rfl
      intro i hmem
      have he := hv i hmem
      rw [Verify, evaluation_commutes S p r hp hr] at he
      rw [he]
    _ = _ := by
      rw [commit_linear_combination, field_lagrange_bridge ids hi I p (lt_of_lt_of_le hp hI),
        field_lagrange_bridge ids hi I r (lt_of_lt_of_le hr hI)]

structure CryptoPedersenVSSGroupSuite : Prop where
  complete : ∀ (q : ℕ) [Fact q.Prime] (B : Type) [Fintype B] [AddCommGroup B]
    [Module (ZMod q) B] (S : CryptoPedersenHomomorphicSum.Setup q B)
    (p r : (ZMod q)[X]) (n : ℕ), p.natDegree < n → r.natDegree < n → ∀ x,
    Verify S n (commitments S p r) x (p.eval x) (r.eval x)
  joint_hiding : ∀ (q : ℕ) [Fact q.Prime] (B : Type) [Fintype B] [AddCommGroup B]
    [Module (ZMod q) B] (S : CryptoPedersenHomomorphicSum.Setup q B)
    (n : ℕ) (m m' : Fin n → ZMod q), coefficientLaw S m = coefficientLaw S m'

theorem verification_suite : CryptoPedersenVSSGroupSuite where
  complete := fun _ _ _ _ _ _ S p r _ hp hr => honest_completeness S p r hp hr
  joint_hiding := fun _ _ _ _ _ _ S _ m m' => coefficient_joint_hiding S m m'

end CryptoPedersenVSSGroup
