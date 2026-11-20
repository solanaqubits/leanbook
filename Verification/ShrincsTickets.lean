/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.ShrincsLeaf
import Verification.SignatureUsageBudget

/-! Registry contract for distinct FXMSS leaves across irreversible ticket charges. -/
namespace ShrincsLeaf
open SignatureUsageBudget

/-- Two signing events on one monotonically advancing ledger.
The middle inequality permits any number of intervening charges. -/
theorem charged_events_distinct {before after later final : Budget} {a b shape depth : Nat}
    (first : issue before 1 = some (after, a)) (forward : after.issued ≤ later.issued)
    (second : issue later 1 = some (final, b)) (hd : depth ≤ 255)
    {p q : Nat × Nat} (ha : select shape depth (some a) = some p)
    (hb : select shape depth (some b) = some q) : p ≠ q := by
  rintro rfl
  have eq := injective_on_success hd ha hb
  have f := accepted_fields first
  have s := accepted_fields second
  omega
structure ShrincsSuite : Prop where
  injective {shape depth a b : Nat} (hd : depth ≤ 255) {p : Nat × Nat}
    (ha : select shape depth (some a) = some p)
    (hb : select shape depth (some b) = some p) : a = b
  distinct {before after later final : Budget} {a b shape depth : Nat}
    (first : issue before 1 = some (after, a)) (forward : after.issued ≤ later.issued)
    (second : issue later 1 = some (final, b)) (hd : depth ≤ 255)
    {p q : Nat × Nat} (ha : select shape depth (some a) = some p)
    (hb : select shape depth (some b) = some q) : p ≠ q

theorem verification_suite : ShrincsSuite :=
  ⟨injective_on_success, charged_events_distinct⟩

end ShrincsLeaf
