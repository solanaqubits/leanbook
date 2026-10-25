/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# ε288: a typed rational polynomial certificate checker

Computable list algorithms, interpreted in the formal polynomial ring.
Soundness is conditional on acceptance. JSON, Python, resource limits and
completeness of the checker are not certified by this module.
-/
namespace AlgebraicCertificateKernel
open scoped BigOperators

/-- Exponent vectors of fixed length, ordered by pure list lexicographic order. -/
abbrev Exponents (n : ℕ) := { l : List ℕ // l.length = n }
abbrev Term (n : ℕ) := Exponents n × ℚ
abbrev SparsePoly (n : ℕ) := List (Term n)
abbrev Polynomial (n : ℕ) := MvPolynomial (Fin n) ℚ

variable {n : ℕ}

def exponent (e : Exponents n) (i : Fin n) : ℕ := e.val[i.val]'(by simp [e.property])

def addExponents (e f : Exponents n) : Exponents n :=
  ⟨List.ofFn (fun i => exponent e i + exponent f i), List.length_ofFn⟩

@[simp] theorem exponent_add (e f : Exponents n) (i : Fin n) :
    exponent (addExponents e f) i = exponent e i + exponent f i := by
  simp [exponent, addExponents]

noncomputable def monomial (e : Exponents n) : Polynomial n :=
  ∏ i : Fin n, MvPolynomial.X i ^ exponent e i

noncomputable def termDenote (t : Term n) : Polynomial n :=
  MvPolynomial.C t.2 * monomial t.1

noncomputable def denote (p : SparsePoly n) : Polynomial n := (p.map termDenote).sum

@[simp] theorem denote_nil : denote ([] : SparsePoly n) = 0 := rfl
@[simp] theorem denote_cons (t : Term n) (p : SparsePoly n) :
    denote (t :: p) = termDenote t + denote p := rfl

def add (p q : SparsePoly n) : SparsePoly n := p ++ q

def smul (r : ℚ) (p : SparsePoly n) : SparsePoly n := p.map (fun t => (t.1, r * t.2))
def neg (p : SparsePoly n) : SparsePoly n := smul (-1) p

def mulTerm (t : Term n) (p : SparsePoly n) : SparsePoly n :=
  p.map (fun u => (addExponents t.1 u.1, t.2 * u.2))

def mul : SparsePoly n → SparsePoly n → SparsePoly n
  | [], _ => []
  | t :: p, q => add (mulTerm t q) (mul p q)

@[simp] theorem denote_add (p q : SparsePoly n) : denote (add p q) = denote p + denote q := by
  simp [add, denote]

@[simp] theorem denote_smul (r : ℚ) (p : SparsePoly n) :
    denote (smul r p) = MvPolynomial.C r * denote p := by
  induction p with
  | nil => simp [smul]
  | cons t p ih =>
    change termDenote (t.1, r * t.2) + denote (smul r p) = _
    rw [ih, denote_cons, mul_add]
    simp [termDenote, map_mul, mul_assoc]

@[simp] theorem denote_neg (p : SparsePoly n) : denote (neg p) = -denote p := by
  simp [neg]

@[simp] theorem monomial_add (e f : Exponents n) :
    monomial (addExponents e f) = monomial e * monomial f := by
  simp [monomial, pow_add, Finset.prod_mul_distrib]

@[simp] theorem denote_mulTerm (t : Term n) (p : SparsePoly n) :
    denote (mulTerm t p) = termDenote t * denote p := by
  induction p with
  | nil => simp [mulTerm]
  | cons u p ih =>
    change termDenote (addExponents t.1 u.1, t.2 * u.2) + denote (mulTerm t p) = _
    rw [ih, denote_cons, mul_add]
    simp [termDenote, map_mul, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem denote_mul (p q : SparsePoly n) : denote (mul p q) = denote p * denote q := by
  induction p with
  | nil => simp [mul]
  | cons t p ih => simp [mul, ih, add_mul]

/-- Exact total coefficient of a vector, allowing repetitions in the input. -/
def coefficient (p : SparsePoly n) (e : Exponents n) : ℚ :=
  (p.map (fun t => if t.1 = e then t.2 else 0)).sum

def support (p : SparsePoly n) : Finset (Exponents n) := (p.map Prod.fst).toFinset

def active (p : SparsePoly n) : Finset (Exponents n) :=
  (support p).filter (fun e => coefficient p e ≠ 0)

/-- Sort distinct active vectors in descending pure lexicographic order. -/
def normalize (p : SparsePoly n) : SparsePoly n :=
  (List.insertionSort (· ≥ ·)
    ((p.map Prod.fst).dedup.filter (fun e => coefficient p e ≠ 0))).map
      (fun e => (e, coefficient p e))

/-- Bridge the explicit list algorithm to the library finite-set sort specification. -/
theorem normalize_eq_sort (p : SparsePoly n) :
    normalize p = ((active p).sort (· ≥ ·)).map (fun e => (e, coefficient p e)) := by
  have hs : (active p).sort (· ≥ ·) = List.insertionSort (· ≥ ·)
      ((p.map Prod.fst).dedup.filter (fun e => coefficient p e ≠ 0)) := by
    simp only [active, support, Finset.sort, List.toFinset, Finset.filter, Multiset.sort,
      List.mergeSort_eq_insertionSort, Multiset.toFinset, Multiset.dedup, Multiset.filter]
    rfl
  rw [hs]
  rfl

theorem denote_eq_sum_coefficient (p : SparsePoly n) (s : Finset (Exponents n))
    (hs : ∀ t ∈ p, t.1 ∈ s) :
    denote p = ∑ e ∈ s, MvPolynomial.C (coefficient p e) * monomial e := by
  induction p with
  | nil => simp [coefficient]
  | cons t p ih =>
    have ht : t.1 ∈ s := hs t (by simp)
    have hp : ∀ u ∈ p, u.1 ∈ s := fun u hu => hs u (by simp [hu])
    rw [denote_cons, ih hp]
    simp only [coefficient, List.map_cons, List.sum_cons, map_add, add_mul,
      Finset.sum_add_distrib]
    congr 1
    simp only [apply_ite, map_zero, ite_mul, zero_mul]
    simp [termDenote, ht]

theorem denote_normalize (p : SparsePoly n) : denote (normalize p) = denote p := by
  rw [denote_eq_sum_coefficient p (support p) (by
    intro t ht; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩))]
  rw [normalize_eq_sort]
  unfold denote
  simp only [List.map_map, Function.comp_def, termDenote]
  rw [← List.sum_toFinset _ ((active p).sort_nodup (· ≥ ·)), Finset.sort_toFinset]
  unfold active
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with h
  · rfl
  · simp_all

theorem normalize_strict_order (p : SparsePoly n) :
    (normalize p).Pairwise (fun a b => b.1 < a.1) := by
  rw [normalize_eq_sort, List.pairwise_map]
  exact (active p).sortedGT_sort.pairwise

theorem normalize_no_duplicates (p : SparsePoly n) :
    ((normalize p).map Prod.fst).Nodup := by
  simpa only [normalize_eq_sort, List.map_map, Function.comp_def, List.map_id'] using
    (active p).sort_nodup (· ≥ ·)

theorem normalize_nonzero (p : SparsePoly n) : ∀ t ∈ normalize p, t.2 ≠ 0 := by
  intro t ht
  rw [normalize_eq_sort] at ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  exact (Finset.mem_filter.mp ((Finset.mem_sort (· ≥ ·)).mp he)).2

/-- One common finite index type rules out missing or excess multipliers. -/
structure Passport (n m : ℕ) where
  hypotheses : Fin m → SparsePoly n
  target : SparsePoly n

structure Certificate (n m : ℕ) where
  multipliers : Fin m → SparsePoly n

def combination {m : ℕ} (p : Passport n m) (c : Certificate n m) : SparsePoly n :=
  (List.ofFn (fun i => mul (c.multipliers i) (p.hypotheses i))).flatten

def residual {m : ℕ} (p : Passport n m) (c : Certificate n m) : SparsePoly n :=
  add p.target (neg (combination p c))

def isZero (p : SparsePoly n) : Bool := p.isEmpty

def checkCert {m : ℕ} (p : Passport n m) (c : Certificate n m) : Bool :=
  isZero (normalize (residual p c))

theorem denote_flatten (ps : List (SparsePoly n)) :
    denote ps.flatten = (ps.map denote).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [denote, List.map_append, List.sum_append] using ih

theorem denote_combination {m : ℕ} (p : Passport n m) (c : Certificate n m) :
    denote (combination p c) =
      ∑ i, denote (c.multipliers i) * denote (p.hypotheses i) := by
  simp [combination, denote_flatten, List.map_ofFn, Function.comp_def, List.sum_ofFn]

theorem checkCert_sound {m : ℕ} (p : Passport n m) (c : Certificate n m)
    (h : checkCert p c = true) :
    denote p.target = ∑ i, denote (c.multipliers i) * denote (p.hypotheses i) := by
  have hz : normalize (residual p c) = [] := List.isEmpty_iff.mp h
  have hd := congrArg denote hz
  rw [denote_normalize, denote_nil] at hd
  simpa [residual, denote_combination, ← sub_eq_add_neg, sub_eq_zero] using hd

theorem eval_soundness {m : ℕ} (p : Passport n m) (c : Certificate n m)
    (h : checkCert p c = true) (v : Fin n → ℚ)
    (hv : ∀ i, MvPolynomial.eval v (denote (p.hypotheses i)) = 0) :
    MvPolynomial.eval v (denote p.target) = 0 := by
  rw [checkCert_sound p c h]
  simp [hv]

/-- Registry contract for the typed algorithm; no claim about JSON translation. -/
structure AlgebraicCertificateSuite : Prop where
  addition : ∀ {n} (p q : SparsePoly n), denote (add p q) = denote p + denote q
  multiplication : ∀ {n} (p q : SparsePoly n), denote (mul p q) = denote p * denote q
  scaling : ∀ {n} (r : ℚ) (p : SparsePoly n),
    denote (smul r p) = MvPolynomial.C r * denote p
  negation : ∀ {n} (p : SparsePoly n), denote (neg p) = -denote p
  normalization : ∀ {n} (p : SparsePoly n), denote (normalize p) = denote p
  strict_order : ∀ {n} (p : SparsePoly n),
    (normalize p).Pairwise (fun a b => b.1 < a.1)
  no_duplicates : ∀ {n} (p : SparsePoly n), ((normalize p).map Prod.fst).Nodup
  nonzero : ∀ {n} (p : SparsePoly n), ∀ t ∈ normalize p, t.2 ≠ 0
  sound : ∀ {n m} (p : Passport n m) (c : Certificate n m), checkCert p c = true →
    denote p.target = ∑ i, denote (c.multipliers i) * denote (p.hypotheses i)
  evaluation : ∀ {n m} (p : Passport n m) (c : Certificate n m),
    checkCert p c = true → ∀ v : Fin n → ℚ,
    (∀ i, MvPolynomial.eval v (denote (p.hypotheses i)) = 0) →
    MvPolynomial.eval v (denote p.target) = 0

theorem verification_suite : AlgebraicCertificateSuite := {
  addition := denote_add
  multiplication := denote_mul
  scaling := denote_smul
  negation := denote_neg
  normalization := denote_normalize
  strict_order := normalize_strict_order
  no_duplicates := normalize_no_duplicates
  nonzero := normalize_nonzero
  sound := checkCert_sound
  evaluation := eval_soundness
}

end AlgebraicCertificateKernel
