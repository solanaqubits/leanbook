/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.AlgebraicCertificateKernel

/-!
# ALCC coefficient-caching normalization pilot

Compute each distinct coefficient once before filtering and sorting. Exact list
equality, not only polynomial denotation, is the refinement contract. This pilot
does not replace the production checker or claim a runtime cost theorem.
-/
namespace AlgebraicCertificateNormalizeCached
open AlgebraicCertificateKernel

/-- Keep the coefficient in the sortable record instead of recomputing it. -/
def normalizeCached {n : ℕ} (p : SparsePoly n) : SparsePoly n :=
  List.insertionSort (fun a b => a.1 ≥ b.1)
    (((p.map Prod.fst).dedup.map (fun e => (e, coefficient p e))).filter
      (fun t => decide (t.2 ≠ 0)))

/-- All dimensions, rational coefficients, duplicates and cancellations are covered. -/
theorem normalizeCached_eq {n : ℕ} (p : SparsePoly n) :
    normalizeCached p = normalize p := by
  unfold normalizeCached normalize
  rw [List.filter_map]
  symm
  exact List.map_insertionSort (fun (a b : Exponents n) => a ≥ b)
    (fun (a b : Term n) => a.1 ≥ b.1) (fun e => (e, coefficient p e))
    _ (by intros; rfl)

theorem denote_normalizeCached {n : ℕ} (p : SparsePoly n) :
    denote (normalizeCached p) = denote p := by
  rw [normalizeCached_eq, denote_normalize]

/-- An alternative checker has exactly the same Bool result on every typed input. -/
theorem checkCert_cached_eq {n m : ℕ} (p : Passport n m) (c : Certificate n m) :
    isZero (normalizeCached (residual p c)) = checkCert p c := by
  rw [normalizeCached_eq]
  rfl

end AlgebraicCertificateNormalizeCached
