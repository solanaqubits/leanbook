/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPABoundedRetryContract
import Mathlib.Data.Fintype.BigOperators

/-! Checked finite candidates and independent product tapes. Completed child responses
remain inputs; no recursive response generation, ROM or runtime bound is claimed. -/
namespace CryptoBulletproofsIPAProductTapeCandidateGeneratorContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
open CryptoBulletproofsIPAForkingExtractionContract
open CryptoBulletproofsIPAFiniteForkingProbabilityContract
open CryptoBulletproofsIPATreeProbabilityContract

variable {q : ℕ} [Fact q.Prime] {G : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] {k : ℕ}

/-- Retain a response only after validating its independently computed context. -/
def checkedReplies (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (raw : ZMod q → Option (IPATranscriptTree q G k)) (x : ZMod q) :
    Option (IPATranscriptTree q G k) :=
  if hx : x ≠ 0 then
    match raw x with
    | none => none
    | some t => if ValidAcceptingTree (child_statement s msg (Units.mk0 x hx)) t
                then some t else none
  else none

theorem checkedReplies_valid (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (raw : ZMod q → Option (IPATranscriptTree q G k)) (x : ZMod q) (hx : x ≠ 0)
    (t : IPATranscriptTree q G k) (h : checkedReplies s msg raw x = some t) :
    ValidAcceptingTree (child_statement s msg (Units.mk0 x hx)) t := by
  unfold checkedReplies at h
  simp only [dif_pos hx] at h
  split at h
  · contradiction
  · split at h
    · cases Option.some.inj h
      assumption
    · contradiction

@[simp] theorem checkedReplies_zero (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (raw : ZMod q → Option (IPATranscriptTree q G k)) : checkedReplies s msg raw 0 = none := by
  simp [checkedReplies]

theorem checkedReplies_present (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (raw : ZMod q → Option (IPATranscriptTree q G k)) (x : ZMod q)
    (t : IPATranscriptTree q G k) (h : checkedReplies s msg raw x = some t) :
    raw x = some t := by
  unfold checkedReplies at h
  split at h
  · split at h
    · contradiction
    · split at h
      · cases Option.some.inj h
        assumption
      · contradiction
  · contradiction

/-- A common prefix, four distinct-square retained replies; no missing-response fallback. -/
def candidate (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (draws : List (ZMod q)) : Option (IPATranscriptTree q G (k + 1)) :=
  let replies := checkedReplies s msg raw
  if draws ∈ successes (replySet calls replies) 4
  then some (drawTree s msg replies draws) else none

theorem candidate_some_iff (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (draws : List (ZMod q)) :
    (candidate s msg calls raw draws).isSome = true ↔
      draws ∈ successes (replySet calls (checkedReplies s msg raw)) 4 := by
  simp [candidate]

theorem candidate_valid (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (draws : List (ZMod q)) (t : IPATranscriptTree q G (k + 1))
    (h : candidate s msg calls raw draws = some t) : ValidAcceptingTree s t := by
  unfold candidate at h
  dsimp only at h
  split at h
  · cases Option.some.inj h
    exact accepted_draws_valid s msg calls (checkedReplies s msg raw)
      (checkedReplies_valid s msg raw) draws (by assumption)
  · contradiction

def extractCandidate (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (draws : List (ZMod q)) : Except String (TreeExtractionResult q (k + 1)) :=
  match candidate s msg calls raw draws with
  | none => .error "candidateUnavailable"
  | some t => checked_extract s t

theorem extractCandidate_sound (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (draws : List (ZMod q)) (r : TreeExtractionResult q (k + 1))
    (h : extractCandidate s msg calls raw draws = .ok r) : ResultValid s r := by
  unfold extractCandidate at h
  split at h
  · contradiction
  · exact checked_extract_sound _ _ _ h

theorem candidate_extracts (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (draws : List (ZMod q)) (t : IPATranscriptTree q G (k + 1))
    (h : candidate s msg calls raw draws = some t) :
    ∃ r, extractCandidate s msg calls raw draws = .ok r ∧ ResultValid s r := by
  have hv := candidate_valid s msg calls raw draws t h
  exact ⟨extractTree t, by simp [extractCandidate, h, checked_extract, hv],
    tree_extraction_soundness s t hv⟩

/-- Exact finite sampling event, not a postulated ConditionalBounds premise. -/
theorem candidate_probability_eq (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k)) :
    probability (samples calls.toFinset 4)
      ((samples calls.toFinset 4).filter
        (fun l => (candidate s msg calls raw l).isSome = true)) =
      successProbability calls.toFinset (replySet calls (checkedReplies s msg raw)) := by
  have hs := successes_subset_samples (replySet_subset_calls calls (checkedReplies s msg raw)) 4
  have he : (samples calls.toFinset 4).filter
      (fun l => (candidate s msg calls raw l).isSome = true) =
      successes (replySet calls (checkedReplies s msg raw)) 4 := by
    ext l
    simp only [Finset.mem_filter, candidate_some_iff]
    exact and_iff_right_of_imp (fun h => hs h)
  rw [he, probability, Finset.inter_eq_left.mpr hs, card_samples]
  simp only [successProbability, Nat.cast_pow]

theorem candidate_probability_positive (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (h : 7 ≤ (replySet calls (checkedReplies s msg raw)).card) :
    0 < probability (samples calls.toFinset 4)
      ((samples calls.toFinset 4).filter
        (fun l => (candidate s msg calls raw l).isSome = true)) := by
  rw [candidate_probability_eq]
  have hn : (replySet calls (checkedReplies s msg raw)).Nonempty :=
    Finset.card_pos.mp (by omega)
  exact seven_probability_positive _ _ (hn.mono (replySet_subset_calls calls _)) h


section Product
open scoped BigOperators
open CryptoBulletproofsIPABoundedRetryContract
variable {Ω : Type}

/-- All ordered tuples; uniform sampling here is independent sampling with replacement. -/
def productTapes (C : Finset Ω) (T : ℕ) : Finset (Fin T → Ω) :=
  Fintype.piFinset (fun _ => C)

def tapeAttempt (a : Ω → Bool) {T : ℕ} (i : ℕ) (w : Fin T → Ω) : Bool :=
  if hi : i < T then a (w ⟨i, hi⟩) else false

def goodTapes (C : Finset Ω) (a : Ω → Bool) : Finset Ω := C.filter (fun w => a w = true)
def badTapes (C : Finset Ω) (a : Ω → Bool) : Finset Ω := C.filter (fun w => a w = false)
def singleProbability (C : Finset Ω) (a : Ω → Bool) : ℚ := (goodTapes C a).card / C.card

theorem product_card (C : Finset Ω) (T : ℕ) : (productTapes C T).card = C.card ^ T := by
  simp [productTapes]

theorem product_nonempty (C : Finset Ω) (hC : C.Nonempty) (T : ℕ) :
    (productTapes C T).Nonempty := hC.piFinset_const

theorem good_bad_partition (C : Finset Ω) (a : Ω → Bool) :
    (goodTapes C a).card + (badTapes C a).card = C.card := by
  simpa [goodTapes, badTapes, Bool.not_eq_true] using
    Finset.card_filter_add_card_filter_not (s := C) (p := fun w => a w = true)

theorem singleProbability_bounds (C : Finset Ω) (a : Ω → Bool) :
    0 ≤ singleProbability C a ∧ singleProbability C a ≤ 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_filter_le C _) (Nat.cast_nonneg _)

theorem failure_prefix_product (C : Finset Ω) (a : Ω → Bool) (T i : ℕ) (hi : i ≤ T) :
    failures (productTapes C T) (tapeAttempt a) i =
      Fintype.piFinset (fun j : Fin T => if j.val < i then badTapes C a else C) := by
  classical
  ext w
  simp only [failures, Finset.mem_filter, productTapes, Fintype.mem_piFinset,
    firstSuccess_none]
  constructor
  · rintro ⟨hc, hf⟩ j
    split
    · rename_i hj
      exact Finset.mem_filter.mpr ⟨hc j, by simpa [tapeAttempt, j.isLt] using hf j.val hj⟩
    · exact hc j
  · intro hw
    constructor
    · intro j
      specialize hw j
      split at hw
      · exact (Finset.mem_filter.mp hw).1
      · exact hw
    · intro j hj
      have hT : j < T := lt_of_lt_of_le hj hi
      have h := hw ⟨j,hT⟩
      have hb : w ⟨j,hT⟩ ∈ badTapes C a := by simpa [hj] using h
      simpa [tapeAttempt, hT] using (Finset.mem_filter.mp hb).2

theorem prefix_product_count (C B : Finset Ω) (T i : ℕ) (hi : i ≤ T) :
    (∏ j : Fin T, (if j.val < i then B else C).card) = B.card ^ i * C.card ^ (T-i) := by
  induction T generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst i
    simp
  | succ T ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte, Fin.val_succ,
        Nat.succ_lt_succ_iff]
      rw [ih i (by omega)]
      simp [pow_succ, Nat.mul_assoc, Nat.mul_comm]

theorem failure_prefix_count (C : Finset Ω) (a : Ω → Bool) (T i : ℕ) (hi : i ≤ T) :
    (failures (productTapes C T) (tapeAttempt a) i).card =
      (badTapes C a).card ^ i * C.card ^ (T-i) := by
  classical
  rw [failure_prefix_product C a T i hi, Fintype.card_piFinset]
  exact prefix_product_count C _ T i hi

theorem bad_rate (C : Finset Ω) (hC : C.Nonempty) (a : Ω → Bool) :
    ((badTapes C a).card : ℚ) / C.card = 1 - singleProbability C a := by
  have hn : (C.card : ℚ) ≠ 0 := by exact_mod_cast hC.card_pos.ne'
  have hp : ((goodTapes C a).card : ℚ) + (badTapes C a).card = C.card :=
    by exact_mod_cast good_bad_partition C a
  unfold singleProbability
  field_simp
  linarith

theorem failure_step_exact (C : Finset Ω) (hC : C.Nonempty) (a : Ω → Bool)
    (T i : ℕ) (hi : i < T) :
    ((failures (productTapes C T) (tapeAttempt a) (i+1)).card : ℚ) =
      (1-singleProbability C a) * (failures (productTapes C T) (tapeAttempt a) i).card := by
  rw [← bad_rate C hC a, failure_prefix_count C a T (i+1) (by omega),
    failure_prefix_count C a T i (by omega)]
  have hn : (C.card : ℚ) ≠ 0 := by exact_mod_cast hC.card_pos.ne'
  have he : T-i = T-(i+1)+1 := by omega
  simp only [Nat.cast_mul, Nat.cast_pow, he, pow_succ]
  field_simp

/-- Independence is supplied by the concrete product, not an external hypothesis. -/
theorem product_retry_bounds (C : Finset Ω) (hC : C.Nonempty) (a : Ω → Bool) (T : ℕ) :
    RetryBounds (productTapes C T) (tapeAttempt a) (fun _ => singleProbability C a) T := by
  classical
  intro i hi
  exact ⟨(singleProbability_bounds C a).1, (singleProbability_bounds C a).2,
    le_of_eq (failure_step_exact C hC a T i hi)⟩

variable [DecidableEq Ω]

theorem product_failure_probability (C : Finset Ω) (hC : C.Nonempty) (a : Ω → Bool)
    (T i : ℕ) (hi : i ≤ T) :
    probability (productTapes C T) (failures (productTapes C T) (tapeAttempt a) i) =
      (1-singleProbability C a)^i := by
  rw [probability, Finset.inter_eq_left.mpr (show failures (productTapes C T) (tapeAttempt a) i ⊆
      productTapes C T from Finset.filter_subset _ _),
    failure_prefix_count C a T i hi, product_card, ← bad_rate C hC a]
  have hn : (C.card : ℚ) ≠ 0 := by exact_mod_cast hC.card_pos.ne'
  have he : (C.card : ℚ)^T = (C.card : ℚ)^i * (C.card : ℚ)^(T-i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  simp only [Nat.cast_mul, Nat.cast_pow, div_pow]
  rw [he]
  field_simp

/-- Exact complement, including T=0 and success rates zero or one. -/
theorem product_success_probability (C : Finset Ω) (hC : C.Nonempty) (a : Ω → Bool)
    (T : ℕ) :
    probability (productTapes C T)
      (CryptoBulletproofsIPABoundedRetryContract.successes (productTapes C T) (tapeAttempt a) T) =
      1-(1-singleProbability C a)^T := by
  have hn : (0 : ℚ) < (productTapes C T).card :=
    by exact_mod_cast (product_nonempty C hC T).card_pos
  have hp := product_failure_probability C hC a T T le_rfl
  have hc : ((CryptoBulletproofsIPABoundedRetryContract.successes
      (productTapes C T) (tapeAttempt a) T).card : ℚ) +
      (failures (productTapes C T) (tapeAttempt a) T).card = (productTapes C T).card :=
    by exact_mod_cast count_partition (productTapes C T) (tapeAttempt a) T
  rw [probability, Finset.inter_eq_left.mpr (show failures (productTapes C T)
    (tapeAttempt a) T ⊆ productTapes C T from Finset.filter_subset _ _)] at hp
  rw [probability, Finset.inter_eq_left.mpr (show
    CryptoBulletproofsIPABoundedRetryContract.successes (productTapes C T) (tapeAttempt a) T ⊆
    productTapes C T from Finset.filter_subset _ _)]
  apply (div_eq_iff hn.ne').mpr
  have hh := (div_eq_iff hn.ne').mp hp
  nlinarith

omit [DecidableEq Ω] in
theorem product_expected_attempts (C : Finset Ω) (hC : C.Nonempty) (a : Ω → Bool) (T : ℕ) :
    expectedAttempts (productTapes C T) (tapeAttempt a) T =
      ∑ i ∈ Finset.range T, (1-singleProbability C a)^i := by
  classical
  rw [expected_attempts_tail_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact product_failure_probability C hC a T i (Nat.le_of_lt (Finset.mem_range.mp hi))

omit [DecidableEq Ω] in
theorem product_expected_le_inverse (C : Finset Ω) (hC : C.Nonempty) (a : Ω → Bool)
    (hp : 0 < singleProbability C a) (T : ℕ) :
    expectedAttempts (productTapes C T) (tapeAttempt a) T ≤ 1/singleProbability C a := by
  classical
  exact expected_attempts_le_inverse _ (product_nonempty C hC T) _ _ hp
    (singleProbability_bounds C a).2 T (product_retry_bounds C hC a T)


theorem diagonal_success_probability (C : Finset Ω) (a : Ω → Bool) (T : ℕ) (hT : 0 < T) :
    probability C (CryptoBulletproofsIPABoundedRetryContract.successes C (fun _ w => a w) T) =
      singleProbability C a := by
  have he : CryptoBulletproofsIPABoundedRetryContract.successes C (fun _ w => a w) T =
      goodTapes C a := by
    ext w
    have hh : firstSuccess (fun _ => a w) T = none ↔ a w = false :=
      ⟨fun h => (firstSuccess_none _ _).mp h 0 hT,
        fun h => (firstSuccess_none _ _).mpr (fun _ _ => h)⟩
    simp [CryptoBulletproofsIPABoundedRetryContract.successes, goodTapes, hh]
  rw [he, probability, Finset.inter_eq_left.mpr (show goodTapes C a ⊆ C from
    Finset.filter_subset _ _)]
  rfl

theorem diagonal_not_amplified (C : Finset Ω) (a : Ω → Bool) (T : ℕ)
    (hT : 2 ≤ T) (hp : 0 < singleProbability C a) (hp1 : singleProbability C a < 1) :
    probability C (CryptoBulletproofsIPABoundedRetryContract.successes C (fun _ w => a w) T) <
      1-(1-singleProbability C a)^T := by
  rw [diagonal_success_probability C a T (by omega)]
  have hh := pow_lt_self_of_lt_one₀ (by linarith : 0 < 1-singleProbability C a)
    (by linarith : 1-singleProbability C a < 1) (by omega : 1 < T)
  linarith

end Product

section Extraction
open CryptoBulletproofsIPABoundedRetryContract

def candidateAccepted (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (l : List (ZMod q)) : Bool := (candidate s msg calls raw l).isSome

theorem candidate_extraction_event (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (l : List (ZMod q)) :
    (extractCandidate s msg calls raw l).isOk = true ↔ candidateAccepted s msg calls raw l = true :=
    by
  cases h : candidate s msg calls raw l with
  | none => simp [extractCandidate, candidateAccepted, h, Except.isOk, Except.toBool]
  | some t =>
    have hv := candidate_valid s msg calls raw l t h
    simp [extractCandidate, candidateAccepted, h, checked_extract, hv, Except.isOk, Except.toBool]

theorem candidate_single_probability (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k)) :
    singleProbability (samples calls.toFinset 4) (candidateAccepted s msg calls raw) =
      successProbability calls.toFinset (replySet calls (checkedReplies s msg raw)) := by
  have h := candidate_probability_eq s msg calls raw
  rw [probability, Finset.inter_eq_left.mpr (Finset.filter_subset _ _)] at h
  exact h

omit [Fact q.Prime] in
theorem single_space_nonempty (calls : List (ZMod q)) (hc : calls.toFinset.Nonempty) :
    (samples calls.toFinset 4).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_samples]
  exact pow_pos hc.card_pos _

/-- A failed generation is an explicit failure, never a synthetic empty tree. -/
def runProduct (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (T : ℕ) (w : Fin T → List (ZMod q)) : Except String (TreeExtractionResult q (k + 1)) :=
  match firstSuccess (fun i => tapeAttempt (candidateAccepted s msg calls raw) i w) T with
  | none => .error "retryBudgetExhausted"
  | some i => if hi : i < T then extractCandidate s msg calls raw (w ⟨i,hi⟩)
              else .error "indexOutsideBudget"

theorem runProduct_sound (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (T : ℕ) (w : Fin T → List (ZMod q)) (r : TreeExtractionResult q (k + 1))
    (h : runProduct s msg calls raw T w = .ok r) : ResultValid s r := by
  unfold runProduct at h
  split at h
  · contradiction
  · split at h
    · exact extractCandidate_sound _ _ _ _ _ _ h
    · contradiction

theorem runProduct_event (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (raw : ZMod q → Option (IPATranscriptTree q G k))
    (T : ℕ) (w : Fin T → List (ZMod q)) :
    (runProduct s msg calls raw T w).isOk = true ↔
      firstSuccess (fun i => tapeAttempt (candidateAccepted s msg calls raw) i w) T ≠ none := by
  cases h : firstSuccess (fun i => tapeAttempt (candidateAccepted s msg calls raw) i w) T with
  | none => simp [runProduct, h, Except.isOk, Except.toBool]
  | some i =>
    obtain ⟨hi, ha, _⟩ := (firstSuccess_some _ _ _).mp h
    have he := (candidate_extraction_event s msg calls raw (w ⟨i,hi⟩)).mpr
      (by simpa [tapeAttempt, hi] using ha)
    simp [runProduct, h, hi, he]

/-- Derived RetryBounds for the concrete checked candidate experiment. -/
theorem candidate_product_retry_bounds (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (hc : calls.toFinset.Nonempty)
    (raw : ZMod q → Option (IPATranscriptTree q G k)) (T : ℕ) :
    RetryBounds (productTapes (samples calls.toFinset 4) T)
      (tapeAttempt (candidateAccepted s msg calls raw))
      (fun _ => successProbability calls.toFinset (replySet calls (checkedReplies s msg raw))) T :=
    by
  rw [← candidate_single_probability s msg calls raw]
  exact product_retry_bounds _ (single_space_nonempty calls hc) _ T

theorem candidate_product_extraction_probability (s : Statement q G (k + 1))
    (msg : RoundMessages G) (calls : List (ZMod q)) (hc : calls.toFinset.Nonempty)
    (raw : ZMod q → Option (IPATranscriptTree q G k)) (T : ℕ) :
    probability (productTapes (samples calls.toFinset 4) T)
      ((productTapes (samples calls.toFinset 4) T).filter
        (fun w => (runProduct s msg calls raw T w).isOk = true)) =
      1-(1-successProbability calls.toFinset (replySet calls (checkedReplies s msg raw)))^T := by
  have he : (productTapes (samples calls.toFinset 4) T).filter
      (fun w => (runProduct s msg calls raw T w).isOk = true) =
      CryptoBulletproofsIPABoundedRetryContract.successes
        (productTapes (samples calls.toFinset 4) T)
        (tapeAttempt (candidateAccepted s msg calls raw)) T := by
    ext w
    simp only [Finset.mem_filter, runProduct_event,
      CryptoBulletproofsIPABoundedRetryContract.successes, Finset.mem_filter]
  rw [he, product_success_probability _ (single_space_nonempty calls hc),
    candidate_single_probability]

theorem candidate_product_expected_bound (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (hc : calls.toFinset.Nonempty)
    (raw : ZMod q → Option (IPATranscriptTree q G k)) (T : ℕ)
    (hp : 0 < successProbability calls.toFinset (replySet calls (checkedReplies s msg raw))) :
    expectedAttempts (productTapes (samples calls.toFinset 4) T)
      (tapeAttempt (candidateAccepted s msg calls raw)) T ≤
      1/successProbability calls.toFinset (replySet calls (checkedReplies s msg raw)) := by
  rw [← candidate_single_probability s msg calls raw] at hp ⊢
  exact product_expected_le_inverse _ (single_space_nonempty calls hc) _ hp T

end Extraction

open CryptoBulletproofsIPABoundedRetryContract in
structure CryptoBulletproofsIPAProductTapeCandidateGeneratorContractSuite : Prop where
  retries : ∀ (Ω : Type) (C : Finset Ω), C.Nonempty → ∀ a T,
    RetryBounds (productTapes C T) (tapeAttempt a) (fun _ => singleProbability C a) T
  exact_failure : ∀ (Ω : Type) [DecidableEq Ω] (C : Finset Ω), C.Nonempty → ∀ a T,
    probability (productTapes C T) (failures (productTapes C T) (tapeAttempt a) T) =
      (1-singleProbability C a)^T
  expectation : ∀ (Ω : Type) (C : Finset Ω), C.Nonempty → ∀ a,
    0 < singleProbability C a → ∀ T,
      expectedAttempts (productTapes C T) (tapeAttempt a) T ≤ 1/singleProbability C a
  extraction : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (k : ℕ) (s : Statement q G (k + 1)) msg calls raw T w r,
      runProduct s msg calls raw T w = .ok r → ResultValid s r

theorem verification_suite : CryptoBulletproofsIPAProductTapeCandidateGeneratorContractSuite where
  retries := fun _ => product_retry_bounds
  exact_failure := fun _ _ C hC a T => product_failure_probability C hC a T T le_rfl
  expectation := fun _ => product_expected_le_inverse
  extraction := fun _ _ _ _ _ _ _ => runProduct_sound

end CryptoBulletproofsIPAProductTapeCandidateGeneratorContract
