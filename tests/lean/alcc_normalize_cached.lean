import Verification.AlgebraicCertificateNormalizeCached
import Mathlib.Tactic.NormNum

open AlgebraicCertificateKernel AlgebraicCertificateNormalizeCached

example : normalizeCached ([] : SparsePoly 0) = [] := by decide
example : normalizeCached ([((⟨[], rfl⟩ : Exponents 0), 2 / 3),
    (⟨[], rfl⟩, -2 / 3)] : SparsePoly 0) = [] := by
  norm_num [normalizeCached, coefficient, List.insertionSort, List.orderedInsert]
example : normalizeCached ([((⟨[1], rfl⟩ : Exponents 1), 1 / 3),
    (⟨[1], rfl⟩, 1 / 6), (⟨[0], rfl⟩, 0)] : SparsePoly 1) =
    [(⟨[1], rfl⟩, 1 / 2)] := by
  norm_num [normalizeCached, coefficient, List.insertionSort, List.orderedInsert]
example {n : Nat} (p : SparsePoly n) :
    (normalizeCached p).Pairwise (fun a b => b.1 < a.1) := by
  rw [normalizeCached_eq]
  exact normalize_strict_order p
