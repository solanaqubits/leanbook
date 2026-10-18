/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPATreeProbabilityContract

/-! Bounded first-success search on correlated finite tapes. Conditional bounds
are on all preceding failures. Attempt counts are not execution-time bounds. -/
namespace CryptoBulletproofsIPABoundedRetryContract
open scoped BigOperators
open CryptoBulletproofsIPATreeProbabilityContract

/-- Increasing budgets extend the SAME sequence and stop at its first success. -/
def firstSuccess (a : ℕ → Bool) : ℕ → Option ℕ
  | 0 => none
  | T + 1 => match firstSuccess a T with
    | some i => some i
    | none => if a T then some T else none

@[simp] theorem firstSuccess_zero (a : ℕ → Bool) : firstSuccess a 0 = none := rfl

theorem firstSuccess_none (a : ℕ → Bool) (T : ℕ) :
    firstSuccess a T = none ↔ ∀ i < T, a i = false := by
  induction T with
  | zero => simp [firstSuccess]
  | succ T ih =>
    cases h : firstSuccess a T with
    | none =>
      have hh := ih.mp h
      simp only [firstSuccess, h]
      cases ha : a T
      · simp only [Bool.false_eq_true, ↓reduceIte, Order.lt_add_one_iff, true_iff]
        intro i hi
        rcases Nat.lt_or_eq_of_le hi with hi | rfl
        · exact hh i hi
        · exact ha
      · simp only [↓reduceIte, reduceCtorEq, Order.lt_add_one_iff, false_iff,
          not_forall, Bool.not_eq_false]
        exact ⟨T, le_rfl, ha⟩
    | some j =>
      simp only [firstSuccess, h, Option.some_ne_none, false_iff]
      intro hh
      have : firstSuccess a T = none := ih.mpr (fun i hi => hh i (Nat.lt_succ_of_lt hi))
      simp [h] at this

theorem firstSuccess_some (a : ℕ → Bool) (T i : ℕ) :
    firstSuccess a T = some i ↔ i < T ∧ a i = true ∧ ∀ j < i, a j = false := by
  induction T generalizing i with
  | zero => simp [firstSuccess]
  | succ T ih =>
    cases h : firstSuccess a T with
    | none =>
      have hh := (firstSuccess_none a T).mp h
      simp only [firstSuccess, h]
      constructor
      · split
        · intro he
          have heq : T = i := Option.some.inj he
          subst i
          exact ⟨Nat.lt_succ_self T, by assumption, hh⟩
        · simp
      · rintro ⟨hi, ha, hb⟩
        have he : i = T := by
          by_contra he
          have hf := hh i (by omega)
          simp [ha] at hf
        subst i
        simp [ha]
    | some j =>
      have hj := (ih j).mp h
      simp only [firstSuccess, h, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨Nat.lt_succ_of_lt hj.1, hj.2⟩
      · rintro ⟨_, ha, hb⟩
        by_contra he
        rcases lt_or_gt_of_ne he with hij | hij
        · have hf := hb j hij
          simp [hj.2.1] at hf
        · have hf := hj.2.2 i hij
          simp [ha] at hf

theorem firstSuccess_extend (a : ℕ → Bool) (T U i : ℕ) (hTU : T ≤ U)
    (h : firstSuccess a T = some i) : firstSuccess a U = some i := by
  obtain ⟨hi, ha, hb⟩ := (firstSuccess_some a T i).mp h
  exact (firstSuccess_some a U i).mpr ⟨lt_of_lt_of_le hi hTU, ha, hb⟩

/-- Actual attempts: increment exactly when no earlier success was found. -/
def attempts (a : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | T + 1 => attempts a T + if firstSuccess a T = none then 1 else 0

theorem attempts_le (a : ℕ → Bool) (T : ℕ) : attempts a T ≤ T := by
  induction T with
  | zero => rfl
  | succ T ih => simp only [attempts]; split <;> omega

theorem attempts_none (a : ℕ → Bool) (T : ℕ) (h : firstSuccess a T = none) :
    attempts a T = T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have hh := (firstSuccess_none a (T+1)).mp h
    have ht := (firstSuccess_none a T).mpr (fun i hi => hh i (Nat.lt_succ_of_lt hi))
    simp [attempts, ht, ih ht]

theorem attempts_some (a : ℕ → Bool) (T i : ℕ) (h : firstSuccess a T = some i) :
    attempts a T = i + 1 := by
  induction T with
  | zero => simp [firstSuccess] at h
  | succ T ih =>
    cases ht : firstSuccess a T with
    | none =>
      have he : i = T := ((by simpa [firstSuccess, ht] using h : a T = true ∧ T = i).2).symm
      subst i
      simp [attempts, ht, attempts_none a T ht]
    | some j =>
      have he : j = i := by simpa [firstSuccess, ht] using h
      subst j
      simp [attempts, ht, ih ht]

section Finite
variable {Ω : Type} [DecidableEq Ω]

def failures (C : Finset Ω) (a : ℕ → Ω → Bool) (T : ℕ) : Finset Ω :=
  C.filter (fun w => firstSuccess (fun i => a i w) T = none)

def successes (C : Finset Ω) (a : ℕ → Ω → Bool) (T : ℕ) : Finset Ω :=
  C.filter (fun w => firstSuccess (fun i => a i w) T ≠ none)

omit [DecidableEq Ω] in
@[simp] theorem failures_zero (C : Finset Ω) (a : ℕ → Ω → Bool) : failures C a 0 = C := by
  simp [failures]

omit [DecidableEq Ω] in
theorem failures_succ (C : Finset Ω) (a : ℕ → Ω → Bool) (T : ℕ) :
    failures C a (T+1) = (failures C a T).filter (fun w => a T w = false) := by
  ext w
  simp only [failures, Finset.mem_filter]
  cases h : firstSuccess (fun i => a i w) T <;> cases ha : a T w <;>
    simp [firstSuccess, h, ha]

omit [DecidableEq Ω] in
theorem count_partition (C : Finset Ω) (a : ℕ → Ω → Bool) (T : ℕ) :
    (successes C a T).card + (failures C a T).card = C.card := by
  simpa [successes, failures] using Finset.card_filter_add_card_filter_not
    (s := C) (p := fun w => firstSuccess (fun i => a i w) T ≠ none)

/-- Conditional on all earlier failures; no division by an empty prefix. -/
def RetryBounds (C : Finset Ω) (a : ℕ → Ω → Bool) (p : ℕ → ℚ) (T : ℕ) : Prop :=
  ∀ i < T, 0 ≤ p i ∧ p i ≤ 1 ∧
    ((failures C a (i+1)).card : ℚ) ≤ (1-p i) * (failures C a i).card

instance retryBoundsDecidable (C : Finset Ω) (a : ℕ → Ω → Bool) (p : ℕ → ℚ) (T : ℕ) :
    Decidable (RetryBounds C a p T) := by unfold RetryBounds; infer_instance

omit [DecidableEq Ω] in
theorem failure_count_bound (C : Finset Ω) (a : ℕ → Ω → Bool) (p : ℕ → ℚ)
    (T : ℕ) (h : RetryBounds C a p T) :
    ((failures C a T).card : ℚ) ≤ (∏ i ∈ Finset.range T, (1-p i)) * C.card := by
  induction T with
  | zero => simp
  | succ T ih =>
    have step := h T (Nat.lt_succ_self T)
    have prev := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hm := mul_le_mul_of_nonneg_left prev (sub_nonneg.mpr step.2.1)
    rw [Finset.prod_range_succ]
    nlinarith [step.2.2]

theorem failure_probability_bound (C : Finset Ω) (hC : C.Nonempty)
    (a : ℕ → Ω → Bool) (p : ℕ → ℚ) (T : ℕ) (h : RetryBounds C a p T) :
    probability C (failures C a T) ≤ ∏ i ∈ Finset.range T, (1-p i) := by
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  rw [probability,
    Finset.inter_eq_left.mpr (show failures C a T ⊆ C from Finset.filter_subset _ _)]
  exact (div_le_iff₀ hc).mpr (failure_count_bound C a p T h)

theorem success_probability_bound (C : Finset Ω) (hC : C.Nonempty)
    (a : ℕ → Ω → Bool) (p : ℕ → ℚ) (T : ℕ) (h : RetryBounds C a p T) :
    1 - (∏ i ∈ Finset.range T, (1-p i)) ≤ probability C (successes C a T) := by
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  have hp : ((successes C a T).card : ℚ) + (failures C a T).card = C.card :=
    by exact_mod_cast count_partition C a T
  have hf := failure_count_bound C a p T h
  rw [probability,
    Finset.inter_eq_left.mpr (show successes C a T ⊆ C from Finset.filter_subset _ _)]
  apply (le_div_iff₀ hc).mpr
  nlinarith

theorem constant_success_bound (C : Finset Ω) (hC : C.Nonempty)
    (a : ℕ → Ω → Bool) (p : ℚ) (T : ℕ) (h : RetryBounds C a (fun _ => p) T) :
    1-(1-p)^T ≤ probability C (successes C a T) := by
  simpa using success_probability_bound C hC a (fun _ => p) T h

/-- Finite uniform expectation of the number of attempts actually executed. -/
def expectedAttempts (C : Finset Ω) (a : ℕ → Ω → Bool) (T : ℕ) : ℚ :=
  (∑ w ∈ C, (attempts (fun i => a i w) T : ℚ)) / C.card

omit [DecidableEq Ω] in
theorem attempt_sum (C : Finset Ω) (a : ℕ → Ω → Bool) (T : ℕ) :
    (∑ w ∈ C, (attempts (fun i => a i w) T : ℚ)) =
      ∑ i ∈ Finset.range T, ((failures C a i).card : ℚ) := by
  induction T with
  | zero => simp [attempts]
  | succ T ih =>
    simp only [attempts, Nat.cast_add, Finset.sum_add_distrib, ih, Finset.sum_range_succ]
    congr 1
    simp [failures, Finset.sum_boole]

theorem expected_attempts_tail_sum (C : Finset Ω) (a : ℕ → Ω → Bool) (T : ℕ) :
    expectedAttempts C a T = ∑ i ∈ Finset.range T, probability C (failures C a i) := by
  simp only [expectedAttempts, attempt_sum, Finset.sum_div, probability]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.inter_eq_left.mpr (show failures C a i ⊆ C from Finset.filter_subset _ _)]

omit [DecidableEq Ω] in
theorem expected_attempts_geometric (C : Finset Ω) (hC : C.Nonempty)
    (a : ℕ → Ω → Bool) (p : ℚ) (T : ℕ) (h : RetryBounds C a (fun _ => p) T) :
    expectedAttempts C a T ≤ ∑ i ∈ Finset.range T, (1-p)^i := by
  classical
  rw [expected_attempts_tail_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hh : RetryBounds C a (fun _ => p) i :=
    fun j hj => h j (lt_trans hj (Finset.mem_range.mp hi))
  simpa using failure_probability_bound C hC a (fun _ => p) i hh

end Finite

theorem geometric_telescoping (p : ℚ) (T : ℕ) :
    p * (∑ i ∈ Finset.range T, (1-p)^i) = 1-(1-p)^T := by
  induction T with
  | zero => simp
  | succ T ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith

theorem geometric_le_inverse (p : ℚ) (hp : 0 < p) (hp1 : p ≤ 1) (T : ℕ) :
    (∑ i ∈ Finset.range T, (1-p)^i) ≤ 1/p := by
  apply (le_div_iff₀ hp).mpr
  have ht := geometric_telescoping p T
  have hn : 0 ≤ (1-p)^T := pow_nonneg (sub_nonneg.mpr hp1) T
  nlinarith

theorem expected_attempts_le_inverse {Ω : Type}
    (C : Finset Ω) (hC : C.Nonempty) (a : ℕ → Ω → Bool) (p : ℚ)
    (hp : 0 < p) (hp1 : p ≤ 1) (T : ℕ) (h : RetryBounds C a (fun _ => p) T) :
    expectedAttempts C a T ≤ 1/p :=
  (expected_attempts_geometric C hC a p T h).trans (geometric_le_inverse p hp hp1 T)


open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
section IPA
variable {q : ℕ} [Fact q.Prime] {G : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] {k : ℕ}

def checkedAttempt {Ω : Type} (s : Statement q G k)
    (generate : ℕ → Ω → IPATranscriptTree q G k) (i : ℕ) (w : Ω) : Bool :=
  (checked_extract s (generate i w)).isOk

/-- Exhaustion is distinct from a verified witness/relation result. -/
def boundedExtract {Ω : Type} (s : Statement q G k)
    (generate : ℕ → Ω → IPATranscriptTree q G k) (T : ℕ) (w : Ω) :
    Except String (TreeExtractionResult q k) :=
  match firstSuccess (fun i => checkedAttempt s generate i w) T with
  | none => .error "retryBudgetExhausted"
  | some i => checked_extract s (generate i w)

theorem boundedExtract_sound {Ω : Type} (s : Statement q G k)
    (generate : ℕ → Ω → IPATranscriptTree q G k) (T : ℕ) (w : Ω)
    (r : TreeExtractionResult q k) (h : boundedExtract s generate T w = .ok r) :
    ResultValid s r := by
  unfold boundedExtract at h
  split at h
  · contradiction
  · exact checked_extract_sound _ _ _ h

theorem boundedExtract_event {Ω : Type} (s : Statement q G k)
    (generate : ℕ → Ω → IPATranscriptTree q G k) (T : ℕ) (w : Ω) :
    (boundedExtract s generate T w).isOk = true ↔
      firstSuccess (fun i => checkedAttempt s generate i w) T ≠ none := by
  cases h : firstSuccess (fun i => checkedAttempt s generate i w) T with
  | none => simp [boundedExtract, h, Except.isOk, Except.toBool]
  | some i =>
    have hi := ((firstSuccess_some _ _ _).mp h).2.1
    simp only [boundedExtract, h, ne_eq, Option.some_ne_none, not_false_eq_true, iff_true]
    exact hi

theorem boundedExtract_extend {Ω : Type} (s : Statement q G k)
    (generate : ℕ → Ω → IPATranscriptTree q G k) (T U : ℕ) (w : Ω) (hTU : T ≤ U)
    (h : (boundedExtract s generate T w).isOk = true) :
    boundedExtract s generate U w = boundedExtract s generate T w := by
  have hn := (boundedExtract_event s generate T w).mp h
  cases ht : firstSuccess (fun i => checkedAttempt s generate i w) T with
  | none => exact (hn ht).elim
  | some i =>
    have hu := firstSuccess_extend _ T U i hTU ht
    simp [boundedExtract, ht, hu]

/-- Local epsilon205 bounds are required on the surviving failure tapes, with
its ordered checks already conditioned on all previous successes INSIDE a tree. -/
theorem conditional_tree_retry_bounds {Ω : Type}
    (C : Finset Ω) (s : Statement q G k) (generate : ℕ → Ω → IPATranscriptTree q G k)
    (p : ℕ → ℚ) (bs : ℕ → List ℚ) (T : ℕ)
    (hp : ∀ i < T, 0 ≤ p i ∧ p i ≤ 1 ∧ p i ≤ (bs i).prod)
    (hb : ∀ i < T, ConditionalBounds (failures C (checkedAttempt s generate) i)
      (treeTests s (generate i)) (bs i)) :
    RetryBounds C (checkedAttempt s generate) p T := by
  intro i hi
  refine ⟨(hp i hi).1, (hp i hi).2.1, ?_⟩
  let F := failures C (checkedAttempt s generate) i
  have lower := sequential_count_lower F (treeTests s (generate i)) (bs i) (hb i hi)
  rw [passing_treeTests, ← extractor_event_eq] at lower
  have scale := mul_le_mul_of_nonneg_right (hp i hi).2.2 (show (0 : ℚ) ≤ F.card by positivity)
  have partition : ((F.filter (fun w => checkedAttempt s generate i w = true)).card : ℚ) +
      (F.filter (fun w => checkedAttempt s generate i w = false)).card = F.card := by
    exact_mod_cast (show (F.filter (fun w => checkedAttempt s generate i w = true)).card +
      (F.filter (fun w => checkedAttempt s generate i w = false)).card = F.card from by
        simpa using Finset.card_filter_add_card_filter_not
          (s := F) (p := fun w => checkedAttempt s generate i w = true))
  rw [failures_succ]
  change ((F.filter (fun w => checkedAttempt s generate i w = false)).card : ℚ) ≤
    (1-p i)*F.card
  change (bs i).prod * F.card ≤
    ((F.filter (fun w => checkedAttempt s generate i w = true)).card : ℚ) at lower
  nlinarith

theorem bounded_extraction_probability {Ω : Type} [DecidableEq Ω]
    (C : Finset Ω) (hC : C.Nonempty) (s : Statement q G k)
    (generate : ℕ → Ω → IPATranscriptTree q G k) (p : ℕ → ℚ) (bs : ℕ → List ℚ) (T : ℕ)
    (hp : ∀ i < T, 0 ≤ p i ∧ p i ≤ 1 ∧ p i ≤ (bs i).prod)
    (hb : ∀ i < T, ConditionalBounds (failures C (checkedAttempt s generate) i)
      (treeTests s (generate i)) (bs i)) :
    1-(∏ i ∈ Finset.range T, (1-p i)) ≤
      probability C (C.filter (fun w => (boundedExtract s generate T w).isOk = true)) := by
  have he : C.filter (fun w => (boundedExtract s generate T w).isOk = true) =
      successes C (checkedAttempt s generate) T := by
    ext w
    simp [successes, boundedExtract_event]
  rw [he]
  exact success_probability_bound C hC _ p T
    (conditional_tree_retry_bounds C s generate p bs T hp hb)

theorem positive_bounded_extraction {Ω : Type} [DecidableEq Ω]
    (C : Finset Ω) (s : Statement q G k) (generate : ℕ → Ω → IPATranscriptTree q G k)
    (T : ℕ) (hp : 0 < probability C
      (C.filter (fun w => (boundedExtract s generate T w).isOk = true))) :
    ∃ w ∈ C, ∃ r, boundedExtract s generate T w = .ok r ∧ ResultValid s r := by
  obtain ⟨w, hw, ha⟩ := positive_probability_has_outcome C _ hp
  have hok := (Finset.mem_filter.mp ha).2
  cases h : boundedExtract s generate T w with
  | error e => simp [h, Except.isOk, Except.toBool] at hok
  | ok r => exact ⟨w, hw, r, h, boundedExtract_sound s generate T w r h⟩

end IPA

structure CryptoBulletproofsIPABoundedRetryContractSuite : Prop where
  earliest : ∀ a T i, firstSuccess a T = some i ↔
    i < T ∧ a i = true ∧ ∀ j < i, a j = false
  success : ∀ (Ω : Type) [DecidableEq Ω] (C : Finset Ω), C.Nonempty →
    ∀ a p T, RetryBounds C a p T →
      1-(∏ i ∈ Finset.range T, (1-p i)) ≤ probability C (successes C a T)
  expectation : ∀ (Ω : Type) [DecidableEq Ω] (C : Finset Ω), C.Nonempty →
    ∀ a p, 0 < p → p ≤ 1 → ∀ T, RetryBounds C a (fun _ => p) T →
      expectedAttempts C a T ≤ 1/p
  extraction : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (k : ℕ) (Ω : Type) (s : Statement q G k)
    (generate : ℕ → Ω → IPATranscriptTree q G k) T w r,
      boundedExtract s generate T w = .ok r → ResultValid s r

theorem verification_suite : CryptoBulletproofsIPABoundedRetryContractSuite where
  earliest := firstSuccess_some
  success := fun _ _ => success_probability_bound
  expectation := fun _ _ => expected_attempts_le_inverse
  extraction := fun _ _ _ _ _ _ _ _ => boundedExtract_sound

end CryptoBulletproofsIPABoundedRetryContract
