/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.AlgebraicCertificateKernel

/-!
# Completeness and sound rejection for the typed ALCC checker

A companion to ε288: the original computable kernel and its byte pin are unchanged.
These theorems concern a supplied typed certificate, not certificate search or JSON refinement.
-/
namespace AlgebraicCertificateCompleteness
open AlgebraicCertificateKernel
open scoped BigOperators

variable {n : ℕ}

/-- Standard finitely supported multi-index for a fixed-length exponent vector. -/
noncomputable def exponentIndex (e : Exponents n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (exponent e)

theorem exponentIndex_injective : Function.Injective (exponentIndex (n := n)) := by
  intro e f h
  have he : exponent e = exponent f := congrArg (fun g : Fin n →₀ ℕ => (g : Fin n → ℕ)) h
  apply Subtype.ext
  apply List.ext_getElem (by simp [e.property, f.property])
  intro i hi hj
  exact congrFun he ⟨i, by simpa [e.property] using hi⟩

theorem termDenote_eq_monomial (t : Term n) :
    termDenote t = MvPolynomial.monomial (exponentIndex t.1) t.2 := by
  rw [MvPolynomial.monomial_eq]
  simp [termDenote, monomial, Finsupp.prod_fintype, exponentIndex]

/-- The sparse coefficient sum is exactly the coefficient in the formal polynomial ring. -/
theorem coeff_denote (p : SparsePoly n) (e : Exponents n) :
    MvPolynomial.coeff (exponentIndex e) (denote p) = coefficient p e := by
  induction p with
  | nil => simp [coefficient]
  | cons t p ih =>
    simp [denote_cons, coefficient, termDenote_eq_monomial, MvPolynomial.coeff_monomial,
      exponentIndex_injective.eq_iff, ih]

/-- Completeness of normalization, including repetitions and cancellations in the input. -/
theorem denote_zero_iff_normalize_nil (p : SparsePoly n) :
    denote p = 0 ↔ normalize p = [] := by
  constructor
  · intro h
    have hc : ∀ e, coefficient p e = 0 := by
      intro e
      rw [← coeff_denote, h]
      simp
    have ha : active p = ∅ := by
      ext e
      simp [active, hc]
    simp [normalize_eq_sort, ha]
  · intro h
    rw [← denote_normalize p, h, denote_nil]

theorem checkCert_true_iff_residual_zero {m : ℕ} (p : Passport n m) (c : Certificate n m) :
    checkCert p c = true ↔ denote (residual p c) = 0 := by
  rw [denote_zero_iff_normalize_nil]
  exact List.isEmpty_iff

theorem checkCert_true_iff_identity {m : ℕ} (p : Passport n m) (c : Certificate n m) :
    checkCert p c = true ↔
      denote p.target = ∑ i, denote (c.multipliers i) * denote (p.hypotheses i) := by
  rw [checkCert_true_iff_residual_zero]
  simp [residual, denote_combination, ← sub_eq_add_neg, sub_eq_zero]

/-- Rejection certifies a nonzero residual in the formal polynomial ring. -/
theorem checkCert_false_sound {m : ℕ} (p : Passport n m) (c : Certificate n m)
    (h : checkCert p c = false) : denote (residual p c) ≠ 0 := by
  intro hz
  have ht := (checkCert_true_iff_residual_zero p c).mpr hz
  simp [h] at ht

theorem checkCert_false_iff_residual_ne_zero {m : ℕ} (p : Passport n m) (c : Certificate n m) :
    checkCert p c = false ↔ denote (residual p c) ≠ 0 := by
  constructor
  · exact checkCert_false_sound p c
  · intro h
    cases hc : checkCert p c with
    | false => rfl
    | true => exact False.elim (h ((checkCert_true_iff_residual_zero p c).mp hc))

/-- Registry contract for completeness of a supplied typed certificate. -/
structure AlgebraicCertificateCompletenessSuite : Prop where
  normalization : ∀ (n : ℕ) (p : SparsePoly n), denote p = 0 ↔ normalize p = []
  acceptance : ∀ (n m : ℕ) (p : Passport n m) (c : Certificate n m),
    checkCert p c = true ↔ denote (residual p c) = 0
  rejection : ∀ (n m : ℕ) (p : Passport n m) (c : Certificate n m),
    checkCert p c = false ↔ denote (residual p c) ≠ 0

theorem verification_suite : AlgebraicCertificateCompletenessSuite where
  normalization := fun _ => denote_zero_iff_normalize_nil
  acceptance := fun _ _ => checkCert_true_iff_residual_zero
  rejection := fun _ _ => checkCert_false_iff_residual_ne_zero

end AlgebraicCertificateCompleteness
