/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaMinimumContract

/-! Materialized quota rows and exact equality with the reference recursion.
Every next-row entry reads the same immutable previous row. Equalities hold for
all rational profiles, including profiles outside probability ranges. The search
adapter rebuilds rows per candidate budget: it is not a streaming search, and no
runtime, allocation or bit-complexity improvement is asserted here. -/
namespace CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaBudgetContract
open CryptoHiddenScalarQuotaMinimumContract

/-- States `0..n`, including the absorbing boundary, at budget zero. -/
def quotaInitialRow (n : ℕ) : Vector ℚ (n + 1) :=
  Vector.ofFn fun i => if n ≤ i.val then 1 else 0

/-- A fresh materialized row; both successors are read from `old`. -/
def quotaNextRow (n : ℕ) (p : ℕ → ℚ) (old : Vector ℚ (n + 1)) :
    Vector ℚ (n + 1) :=
  Vector.ofFn fun i => if h : n ≤ i.val then 1 else
    (1 - p i.val) * old[i.val] + p i.val * old[i.val + 1]'(by omega)

/-- Iterate rows without retaining an explicit table of all historical rows. -/
def quotaRow (n : ℕ) (p : ℕ → ℚ) : ℕ → Vector ℚ (n + 1)
  | 0 => quotaInitialRow n
  | T + 1 => quotaNextRow n p (quotaRow n p T)

/-- Pointwise row invariant, with no probability-range assumptions. -/
theorem quotaRow_correct (n : ℕ) (p : ℕ → ℚ) (T i : ℕ) (hi : i < n + 1) :
    (quotaRow n p T)[i] = quotaLower n p T i := by
  induction T generalizing i with
  | zero => simp [quotaRow, quotaInitialRow, quotaLower]
  | succ T ih =>
    simp only [quotaRow, quotaNextRow, Vector.getElem_ofFn]
    by_cases h : n ≤ i
    · simp [h]
    · simp only [h, ↓reduceDIte, quotaLower, if_false]
      rw [ih i hi, ih (i + 1) (by omega)]

/-- Scalar adapter: out-of-row states are already absorbed. -/
def quotaLowerTabular (n : ℕ) (p : ℕ → ℚ) (T j : ℕ) : ℚ :=
  if h : j < n then (quotaRow n p T)[j]'(by omega) else 1

theorem quotaLowerTabular_eq (n : ℕ) (p : ℕ → ℚ) (T j : ℕ) :
    quotaLowerTabular n p T j = quotaLower n p T j := by
  by_cases h : j < n
  · simp [quotaLowerTabular, h, quotaRow_correct]
  · simp [quotaLowerTabular, h, quota_full n p T j (by omega)]

def quotaDeficitTabular (n : ℕ) (p : ℕ → ℚ) (T j : ℕ) : ℚ :=
  1 - quotaLowerTabular n p T j

theorem quotaDeficitTabular_eq (n : ℕ) (p : ℕ → ℚ) (T j : ℕ) :
    quotaDeficitTabular n p T j = quotaDeficit n p T j := by
  simp [quotaDeficitTabular, quotaLowerTabular_eq, quotaDeficit]

/-- Inclusive bounded search with fresh tabular evaluation per candidate. -/
def chooseQuotaBudgetTabularWithin (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) : Option ℕ :=
  searchThrough (fun T => quotaDeficitTabular n p T j ≤ ε) cap

/-- Exact `Option` equality, including `none`, negative tolerances and `cap = 0`. -/
theorem chooseQuotaBudgetTabularWithin_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) :
    chooseQuotaBudgetTabularWithin n p j ε cap = chooseQuotaBudgetWithin n p j ε cap := by
  simp only [chooseQuotaBudgetTabularWithin, quotaDeficitTabular_eq, chooseQuotaBudgetWithin]

structure CryptoHiddenScalarQuotaTabularContractSuite : Prop where
  rows : ∀ n p T i (hi : i < n + 1), (quotaRow n p T)[i] = quotaLower n p T i
  scalar : ∀ n p T j, quotaLowerTabular n p T j = quotaLower n p T j
  deficit : ∀ n p T j, quotaDeficitTabular n p T j = quotaDeficit n p T j
  search : ∀ n p j ε cap,
    chooseQuotaBudgetTabularWithin n p j ε cap = chooseQuotaBudgetWithin n p j ε cap

theorem verification_suite : CryptoHiddenScalarQuotaTabularContractSuite where
  rows := quotaRow_correct
  scalar := quotaLowerTabular_eq
  deficit := quotaDeficitTabular_eq
  search := chooseQuotaBudgetTabularWithin_eq
end CryptoHiddenScalarQuotaTabularContract
