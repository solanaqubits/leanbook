/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Lean.Elab.Tactic.Omega

/-!
# Irreversible usage tickets for limited-signature keys

A ticket is charged before a signing attempt and is never refunded here.
This is numerical accounting, not a cryptographic security theorem or a proof
that a physical signer obeys the ledger. Key labels do not identify key bytes.
-/
namespace SignatureUsageBudget

structure Budget where
  keyLabel : Nat
  epoch : Nat
  limit : Nat
  issued : Nat
  deriving DecidableEq, Repr

def Valid (b : Budget) : Prop := b.issued ≤ b.limit

/-- Reserve a fresh half-open ticket range; even failed signing uses its ticket. -/
def issue (b : Budget) (count : Nat) : Option (Budget × Nat) :=
  if b.issued + count ≤ b.limit then
    some ({ b with issued := b.issued + count }, b.issued)
  else none

theorem accepted_fields {b next : Budget} {count start : Nat}
    (h : issue b count = some (next, start)) :
    next.keyLabel = b.keyLabel ∧ next.epoch = b.epoch ∧
      next.limit = b.limit ∧ next.issued = b.issued + count ∧ start = b.issued := by
  unfold issue at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · contradiction

theorem accepted_valid {b next : Budget} {count start : Nat}
    (h : issue b count = some (next, start)) : Valid next := by
  unfold issue at h
  split at h
  · cases h
    assumption
  · contradiction

theorem issued_monotone {b next : Budget} {count start : Nat}
    (h : issue b count = some (next, start)) : b.issued ≤ next.issued := by
  have hf := accepted_fields h
  omega

theorem ticket_below_limit {b next : Budget} {count start ticket : Nat}
    (h : issue b count = some (next, start))
    (hhi : ticket < start + count) : ticket < next.limit := by
  have hf := accepted_fields h
  have hv := accepted_valid h
  unfold Valid at hv
  omega

theorem exhausted_rejects {b : Budget} (h : b.issued = b.limit)
    {count : Nat} (hc : 0 < count) : issue b count = none := by
  unfold issue
  split
  · omega
  · rfl

/-- A later allocation starts after every ticket of the earlier range. -/
theorem successive_ranges_disjoint {b mid last : Budget} {n m s t ticket : Nat}
    (h₁ : issue b n = some (mid, s))
    (h₂ : issue mid m = some (last, t))
    (hin : s ≤ ticket ∧ ticket < s + n) : ¬ (t ≤ ticket ∧ ticket < t + m) := by
  have hf₁ := accepted_fields h₁
  have hf₂ := accepted_fields h₂
  omega

/-- The actual signer must independently establish exposure ≤ charged tickets. -/
theorem exposure_bounded {b : Budget} {exposure : Nat}
    (hv : Valid b) (he : exposure ≤ b.issued) : exposure ≤ b.limit := by
  unfold Valid at hv
  omega

/-- Two device allocations must come from a genuinely exclusive global partition. -/
theorem two_device_quota_bound {q₁ q₂ used₁ used₂ limit : Nat}
    (hq : q₁ + q₂ ≤ limit) (h₁ : used₁ ≤ q₁) (h₂ : used₂ ≤ q₂) :
    used₁ + used₂ ≤ limit := by
  omega

example : issue ⟨7, 2, 3, 2⟩ 1 = some (⟨7, 2, 3, 3⟩, 2) := rfl
example : issue ⟨7, 2, 3, 3⟩ 1 = none := rfl
example : issue ⟨7, 2, 3, 2⟩ 2 = none := rfl
example : issue ⟨7, 2, 3, 3⟩ 0 = some (⟨7, 2, 3, 3⟩, 3) := rfl

end SignatureUsageBudget
