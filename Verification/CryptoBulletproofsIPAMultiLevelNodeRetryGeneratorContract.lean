/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPARecursiveTreeGeneratorContract

/-! Fresh independent attempts at every internal node, not retries of a fixed whole tree.
Availability of source messages and scalar proposals remains an explicit condition. -/
namespace CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract
open scoped BigOperators
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
open CryptoBulletproofsIPATreeProbabilityContract
open CryptoBulletproofsIPABoundedRetryContract
open CryptoBulletproofsIPAProductTapeCandidateGeneratorContract
open CryptoBulletproofsIPARecursiveTreeGeneratorContract (Source header header_distinct collect
  collect_some collect_isSome)

def amplify (p : ℚ) (T : ℕ) : ℚ := 1 - (1-p)^T

theorem amplify_nonnegative (p : ℚ) (T : ℕ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ amplify p T := by
  have h := pow_le_one₀ (sub_nonneg.mpr hp1) (show 1-p ≤ 1 by linarith) (n := T)
  unfold amplify
  linarith

theorem amplify_le_one (p : ℚ) (T : ℕ) (hp1 : p ≤ 1) : amplify p T ≤ 1 := by
  unfold amplify
  exact sub_le_self _ (pow_nonneg (sub_nonneg.mpr hp1) T)

theorem amplify_mono_probability (p q : ℚ) (T : ℕ) (hpq : p ≤ q) (hq : q ≤ 1) :
    amplify p T ≤ amplify q T := by
  have h := pow_le_pow_left₀ (sub_nonneg.mpr hq) (show 1-q ≤ 1-p by linarith) T
  unfold amplify
  linarith

theorem amplify_mono_budget (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Monotone (amplify p) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := pow_nonneg (sub_nonneg.mpr hp1) n
  unfold amplify
  rw [pow_succ]
  nlinarith

theorem amplify_strict_budget (p : ℚ) (hp : 0 < p) (hp1 : p < 1) :
    StrictMono (amplify p) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := pow_pos (show 0 < 1-p by linarith) n
  unfold amplify
  rw [pow_succ]
  nlinarith

@[simp] theorem amplify_one (p : ℚ) : amplify p 1 = p := by simp [amplify]
@[simp] theorem amplify_zero_budget (p : ℚ) : amplify p 0 = 0 := by simp [amplify]

theorem amplify_ge_probability (p : ℚ) (T : ℕ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : 1 ≤ T) : p ≤ amplify p T := by
  simpa using amplify_mono_budget p hp hp1 hT

theorem amplify_positive (p : ℚ) (T : ℕ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hT : 1 ≤ T) : 0 < amplify p T :=
  lt_of_lt_of_le hp (amplify_ge_probability p T hp.le hp1 hT)

def lowerBound (budget : ℕ → ℕ) (a b : ℚ) : ℕ → ℚ
  | 0 => b
  | k + 1 => amplify (a * lowerBound budget a b k ^ 4) (budget (k + 1))

theorem lowerBound_bounds (budget : ℕ → ℕ) (a b : ℚ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (k : ℕ) :
    0 ≤ lowerBound budget a b k ∧ lowerBound budget a b k ≤ 1 := by
  induction k with
  | zero => exact ⟨hb, hb1⟩
  | succ k ih =>
    have hp := mul_nonneg ha (pow_nonneg ih.1 4)
    have hp1 : a * lowerBound budget a b k ^ 4 ≤ 1 := by
      exact mul_le_one₀ ha1 (pow_nonneg ih.1 4) (pow_le_one₀ ih.1 ih.2)
    exact ⟨amplify_nonnegative _ _ hp hp1, amplify_le_one _ _ hp1⟩

theorem lowerBound_mono_budget (T U : ℕ → ℕ) (a b : ℚ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hTU : ∀ j, T (j + 1) ≤ U (j + 1)) (k : ℕ) : lowerBound T a b k ≤ lowerBound U a b k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have hT := lowerBound_bounds T a b ha ha1 hb hb1 k
    have hU := lowerBound_bounds U a b ha ha1 hb hb1 k
    have hmul : a * lowerBound T a b k ^ 4 ≤ a * lowerBound U a b k ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT.1 ih 4) ha
    have hp := mul_nonneg ha (pow_nonneg hU.1 4)
    have hp1 : a * lowerBound U a b k ^ 4 ≤ 1 :=
      mul_le_one₀ ha1 (pow_nonneg hU.1 4) (pow_le_one₀ hU.1 hU.2)
    exact (amplify_mono_probability _ _ _ hmul hp1).trans
      (amplify_mono_budget _ hp hp1 (hTU k))

theorem lowerBound_single_budget (a b : ℚ) (k : ℕ) :
    lowerBound (fun _ => 1) a b k =
      CryptoBulletproofsIPARecursiveTreeGeneratorContract.lowerBound a b k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [lowerBound, amplify_one,
      CryptoBulletproofsIPARecursiveTreeGeneratorContract.lowerBound, ih]

theorem lowerBound_ge_single (budget : ℕ → ℕ) (a b : ℚ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hT : ∀ j, 1 ≤ budget (j + 1)) (k : ℕ) :
    CryptoBulletproofsIPARecursiveTreeGeneratorContract.lowerBound a b k ≤
      lowerBound budget a b k := by
  rw [← lowerBound_single_budget]
  exact lowerBound_mono_budget _ _ a b ha ha1 hb hb1 hT k

theorem lowerBound_positive (budget : ℕ → ℕ) (a b : ℚ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hT : ∀ j, 1 ≤ budget (j + 1)) (k : ℕ) : 0 < lowerBound budget a b k := by
  exact lt_of_lt_of_le
    (CryptoBulletproofsIPARecursiveTreeGeneratorContract.lowerBound_positive a b ha hb k)
    (lowerBound_ge_single budget a b ha.le ha1 hb.le hb1 hT k)

/-- A positive lower estimate below one does not force strict growth of actual success:
    the actual one-attempt probability can already equal one. -/
theorem amplify_saturated (T : ℕ) (hT : 0 < T) : amplify 1 T = 1 := by
  simp [amplify, Nat.ne_of_gt hT]

theorem lower_estimate_does_not_force_strict_actual_growth :
    (0 : ℚ) < 1/2 ∧ (1/2 : ℚ) < 1 ∧
      amplify 1 1 = amplify 1 2 := by
  norm_num [amplify]


/-- Return the first available result, with the same index policy as epsilon206. -/
def retry {α : Type} {T : ℕ} (f : Fin T → Option α) : Option α :=
  match firstSuccess (fun i => if hi : i < T then (f ⟨i, hi⟩).isSome else false) T with
  | none => none
  | some i => if hi : i < T then f ⟨i, hi⟩ else none

theorem retry_some {α : Type} {T : ℕ} (f : Fin T → Option α) (v : α)
    (h : retry f = some v) : ∃ i, f i = some v := by
  unfold retry at h
  split at h
  · contradiction
  · split at h
    · exact ⟨_, h⟩
    · contradiction

theorem retry_event {α : Type} {T : ℕ} (f : Fin T → Option α) :
    (retry f).isSome = true ↔
      firstSuccess (fun i => if hi : i < T then (f ⟨i, hi⟩).isSome else false) T ≠ none := by
  cases he : firstSuccess (fun i => if hi : i < T then (f ⟨i, hi⟩).isSome else false) T with
  | none => simp [retry, he]
  | some i =>
    obtain ⟨hi, ha, _⟩ := (firstSuccess_some _ _ _).mp he
    have hs : (f ⟨i, hi⟩).isSome = true := by simpa [hi] using ha
    simp [retry, he, hi, hs]

/-- Every attempt includes a new root seed and four fresh recursively budgeted tapes. -/
def Tape (budget : ℕ → ℕ) (Ω : Type) : ℕ → Type
  | 0 => Ω
  | k + 1 => Fin (budget (k + 1)) → Ω × (Fin 4 → Tape budget Ω k)

instance tapeDecidableEq (budget : ℕ → ℕ) {Ω : Type} [DecidableEq Ω] (k : ℕ) :
    DecidableEq (Tape budget Ω k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq Ω)
  | succ k ih => exact inferInstanceAs
      (DecidableEq (Fin (budget (k + 1)) → Ω × (Fin 4 → Tape budget Ω k)))

def tapes (budget : ℕ → ℕ) {Ω : Type} [DecidableEq Ω] (C : Finset Ω) :
    (k : ℕ) → Finset (Tape budget Ω k)
  | 0 => C
  | k + 1 => productTapes (C ×ˢ Fintype.piFinset (fun _ : Fin 4 => tapes budget C k))
      (budget (k + 1))

theorem tapes_nonempty (budget : ℕ → ℕ) {Ω : Type} [DecidableEq Ω]
    (C : Finset Ω) (hC : C.Nonempty) (k : ℕ) : (tapes budget C k).Nonempty := by
  induction k with
  | zero => exact hC
  | succ k ih => exact product_nonempty _ (hC.product ih.piFinset_const) _

theorem tapes_card (budget : ℕ → ℕ) {Ω : Type} [DecidableEq Ω]
    (C : Finset Ω) (k : ℕ) :
    (tapes budget C (k + 1)).card =
      (C.card * (tapes budget C k).card ^ 4) ^ budget (k + 1) := by
  change (productTapes (C ×ˢ Fintype.piFinset (fun _ : Fin 4 => tapes budget C k))
    (budget (k + 1))).card = _
  rw [CryptoBulletproofsIPAProductTapeCandidateGeneratorContract.product_card]
  simp

variable {q : ℕ} [Fact q.Prime] {G : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] {Ω : Type} {k : ℕ}

/-- Full child regeneration in every attempted node; leaf checking is exactly epsilon208. -/
def generate (budget : ℕ → ℕ) (src : Source q G Ω) : {k : ℕ} → Statement q G k →
    Tape budget Ω k → Option (IPATranscriptTree q G k)
  | 0, s, w => CryptoBulletproofsIPARecursiveTreeGeneratorContract.generate src s w
  | _ + 1, s, w => retry (fun j =>
      match header src s (w j).1 with
      | none => none
      | some (msg, u) =>
        (collect (fun i => generate budget src (child_statement s msg (u i)) ((w j).2 i))).map
          (fun ts => .node s msg (fun i => u i) ts))

def attempt (budget : ℕ → ℕ) (src : Source q G Ω) (s : Statement q G (k + 1))
    (w : Ω × (Fin 4 → Tape budget Ω k)) : Option (IPATranscriptTree q G (k + 1)) :=
  match header src s w.1 with
  | none => none
  | some (msg, u) =>
    (collect (fun i => generate budget src (child_statement s msg (u i)) (w.2 i))).map
      (fun ts => .node s msg (fun i => u i) ts)

theorem generate_node (budget : ℕ → ℕ) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (w : Tape budget Ω (k + 1)) :
    generate budget src s w = retry (fun j => attempt budget src s (w j)) := rfl

theorem generate_valid (budget : ℕ → ℕ) (src : Source q G Ω) (s : Statement q G k)
    (w : Tape budget Ω k) (t : IPATranscriptTree q G k)
    (h : generate budget src s w = some t) : ValidAcceptingTree s t := by
  induction k with
  | zero => exact CryptoBulletproofsIPARecursiveTreeGeneratorContract.generate_valid src s w t h
  | succ k ih =>
    obtain ⟨j, hj⟩ := retry_some _ _ h
    split at hj
    · contradiction
    · rename_i msg u hh
      obtain ⟨ts, ht, he⟩ := Option.map_eq_some_iff.mp hj
      cases he
      refine ⟨rfl, ?_⟩
      rw [dif_pos (fun i => Units.ne_zero (u i))]
      refine ⟨header_distinct src s (w j).1 msg u hh, ?_⟩
      intro i
      simpa only [Units.mk0_val] using ih _ _ _ ((collect_some _ _).mp ht i)

def extract (budget : ℕ → ℕ) (src : Source q G Ω) (s : Statement q G k)
    (w : Tape budget Ω k) : Except String (TreeExtractionResult q k) :=
  match generate budget src s w with
  | none => .error "nodeRetryBudgetExhausted"
  | some t => checked_extract s t

theorem generated_extracts (budget : ℕ → ℕ) (src : Source q G Ω) (s : Statement q G k)
    (w : Tape budget Ω k) (t : IPATranscriptTree q G k)
    (h : generate budget src s w = some t) :
    ∃ r, extract budget src s w = .ok r ∧ ResultValid s r := by
  have hv := generate_valid budget src s w t h
  exact ⟨extractTree t, by simp [extract, h, checked_extract, hv],
    tree_extraction_soundness s t hv⟩

theorem extract_sound (budget : ℕ → ℕ) (src : Source q G Ω) (s : Statement q G k)
    (w : Tape budget Ω k) (r : TreeExtractionResult q k)
    (h : extract budget src s w = .ok r) : ResultValid s r := by
  unfold extract at h
  split at h
  · contradiction
  · exact checked_extract_sound _ _ _ h

section Counting
variable [DecidableEq Ω]

def good (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G k) : Finset (Tape budget Ω k) :=
  (tapes budget C k).filter (fun w => (generate budget src s w).isSome = true)

def rate (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω) (s : Statement q G k) : ℚ :=
  (good budget C src s).card / ((tapes budget C k).card : ℚ)

def attemptTapes (budget : ℕ → ℕ) (C : Finset Ω) (k : ℕ) :
    Finset (Ω × (Fin 4 → Tape budget Ω k)) :=
  C ×ˢ Fintype.piFinset (fun _ : Fin 4 => tapes budget C k)

def attemptRate (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) : ℚ :=
  singleProbability (attemptTapes budget C k) (fun w => (attempt budget src s w).isSome)

theorem rate_bounds (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G k) : 0 ≤ rate budget C src s ∧ rate budget C src s ≤ 1 :=
  singleProbability_bounds (tapes budget C k) (fun w => (generate budget src s w).isSome)

theorem rate_probability (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G k) :
    rate budget C src s = probability (tapes budget C k) (good budget C src s) := by
  simp [probability, rate, good, Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]

/-- Exact independent repetition formula, applied locally to this node's composed attempt. -/
theorem rate_node_exact (budget : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (s : Statement q G (k + 1)) :
    rate budget C src s = amplify (attemptRate budget C src s) (budget (k + 1)) := by
  have hn : (attemptTapes budget C k).Nonempty :=
    hC.product (tapes_nonempty budget C hC k).piFinset_const
  have he : good budget C src s = successes
      (productTapes (attemptTapes budget C k) (budget (k + 1)))
      (tapeAttempt (fun w => (attempt budget src s w).isSome)) (budget (k + 1)) := by
    change (productTapes (attemptTapes budget C k) (budget (k + 1))).filter
      (fun w => (retry (fun j => attempt budget src s (w j))).isSome = true) = _
    ext w
    simp only [Finset.mem_filter, retry_event,
      CryptoBulletproofsIPABoundedRetryContract.successes, Finset.mem_filter, tapeAttempt]
  rw [rate_probability, he]
  exact product_success_probability (attemptTapes budget C k) hn _ _

def rootCount (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (w : Ω) : ℕ :=
  match header src s w with
  | none => 0
  | some (msg, u) => ∏ i, (good budget C src (child_statement s msg (u i))).card

def rootRate (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (w : Ω) : ℚ :=
  match header src s w with
  | none => 0
  | some (msg, u) => ∏ i, rate budget C src (child_statement s msg (u i))

omit [DecidableEq Ω] in
theorem branch_filter {α : Type} (D : Finset α) (f : Fin 4 → α → Bool) :
    (Fintype.piFinset (fun _ : Fin 4 => D)).filter (fun v => ∀ i, f i (v i) = true) =
      Fintype.piFinset (fun i => D.filter (fun t => f i t = true)) := by
  ext v
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

theorem fixed_root_count (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (w : Ω) :
    ((Fintype.piFinset (fun _ : Fin 4 => tapes budget C k)).filter
      (fun v => (attempt budget src s (w, v)).isSome = true)).card =
      rootCount budget C src s w := by
  cases hh : header src s w with
  | none => simp [attempt, hh, rootCount]
  | some p =>
    rcases p with ⟨msg, u⟩
    simp only [attempt, hh, Option.isSome_map, collect_isSome, rootCount]
    rw [branch_filter (tapes budget C k)
      (fun i t => (generate budget src (child_statement s msg (u i)) t).isSome),
      Fintype.card_piFinset]
    rfl

theorem attempt_count (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) :
    (goodTapes (attemptTapes budget C k) (fun w => (attempt budget src s w).isSome)).card =
      ∑ w ∈ C, rootCount budget C src s w := by
  change ((C ×ˢ Fintype.piFinset (fun _ : Fin 4 => tapes budget C k)).filter
    (fun w : Ω × (Fin 4 → Tape budget Ω k) => (attempt budget src s w).isSome = true)).card = _
  simp only [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w _
  simpa only [Finset.card_filter] using fixed_root_count budget C src s w

theorem rootRate_count (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (w : Ω) :
    rootRate budget C src s w = rootCount budget C src s w /
      ((tapes budget C k).card : ℚ) ^ 4 := by
  cases hh : header src s w with
  | none => simp [rootRate, rootCount, hh]
  | some p =>
    rcases p with ⟨msg, u⟩
    simp [rootRate, rootCount, hh, rate, Finset.prod_div_distrib, Nat.cast_prod]

/-- Conditional child independence after fixing the root seed, before retry amplification. -/
theorem attempt_rate_exact (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) :
    attemptRate budget C src s = (∑ w ∈ C, rootRate budget C src s w) / C.card := by
  rw [attemptRate, singleProbability, attempt_count]
  simp only [attemptTapes, Finset.card_product, Fintype.card_piFinset_const,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_sum, rootRate_count, ← Finset.sum_div]
  rw [div_div, mul_comm]

theorem attempt_rate_lower (budget : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (s : Statement q G (k + 1)) (B : Finset Ω) (hB : B ⊆ C)
    (b : ℚ) (hb : 0 ≤ b)
    (h : ∀ w ∈ B, ∃ msg u, header src s w = some (msg, u) ∧
      ∀ i, b ≤ rate budget C src (child_statement s msg (u i))) :
    (B.card / (C.card : ℚ)) * b ^ 4 ≤ attemptRate budget C src s := by
  have hn (w) : 0 ≤ rootRate budget C src s w := by rw [rootRate_count]; positivity
  have hw (w) (hw : w ∈ B) : b ^ 4 ≤ rootRate budget C src s w := by
    obtain ⟨msg, u, he, hv⟩ := h w hw
    simp only [rootRate, he]
    calc b ^ 4 = ∏ _ : Fin 4, b := by simp
         _ ≤ _ := Finset.prod_le_prod (fun _ _ => hb) (fun i _ => hv i)
  have hl := (Finset.sum_le_sum hw).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hB (fun w _ _ => hn w))
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  rw [attempt_rate_exact]
  have hd := div_le_div_of_nonneg_right hl (le_of_lt hc)
  simpa [Finset.sum_const, nsmul_eq_mul, div_mul_eq_mul_div] using hd

/-- The existing local source-density contract suffices; no new whole-tree success premise. -/
theorem recursive_probability_lower (budget : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (a b : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (s : Statement q G k) (h : CryptoBulletproofsIPARecursiveTreeGeneratorContract.Dense
      C src a b s) : lowerBound budget a b k ≤ rate budget C src s := by
  induction k with
  | zero => exact h
  | succ k ih =>
    obtain ⟨B, hB, hd, hv⟩ := h
    have hr := attempt_rate_lower budget C hC src s B hB (lowerBound budget a b k)
      (lowerBound_bounds budget a b ha ha1 hb hb1 k).1 (by
        intro w hw
        obtain ⟨msg, u, he, hc⟩ := hv w hw
        exact ⟨msg, u, he, fun i => ih _ (hc i)⟩)
    have hp := (mul_le_mul_of_nonneg_right hd (by positivity)).trans hr
    rw [rate_node_exact budget C hC]
    exact amplify_mono_probability _ _ _ hp (singleProbability_bounds _ _).2

/-- Exact product construction discharges RetryBounds separately at every node. -/
theorem node_retry_bounds (budget : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (s : Statement q G (k + 1)) :
    RetryBounds (tapes budget C (k + 1))
      (tapeAttempt (fun w => (attempt budget src s w).isSome))
      (fun _ => attemptRate budget C src s) (budget (k + 1)) :=
  product_retry_bounds _ (hC.product (tapes_nonempty budget C hC k).piFinset_const) _ _

/-- More local attempts never reduce actual success in this fixed-source product model. -/
theorem rate_mono_budget (T U : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (hTU : ∀ j, T (j + 1) ≤ U (j + 1)) (s : Statement q G k) :
    rate T C src s ≤ rate U C src s := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have hr : attemptRate T C src s ≤ attemptRate U C src s := by
      rw [attempt_rate_exact, attempt_rate_exact]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro w _
      cases hh : header src s w with
      | none => simp [rootRate, hh]
      | some p =>
        rcases p with ⟨msg, u⟩
        simp only [rootRate, hh]
        exact Finset.prod_le_prod (fun i _ => (rate_bounds T C src _).1)
          (fun i _ => ih (child_statement s msg (u i)))
    rw [rate_node_exact T C hC, rate_node_exact U C hC]
    exact (amplify_mono_probability _ _ _ hr (singleProbability_bounds _ _).2).trans
      (amplify_mono_budget _ (singleProbability_bounds _ _).1
        (singleProbability_bounds _ _).2 (hTU k))

/-- Unit budgets recover the one-pass epsilon208 probability exactly. -/
theorem rate_single_budget (C : Finset Ω) (hC : C.Nonempty) (src : Source q G Ω)
    (s : Statement q G k) : rate (fun _ => 1) C src s =
      CryptoBulletproofsIPARecursiveTreeGeneratorContract.rate C src s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rate_node_exact _ C hC, amplify_one, attempt_rate_exact,
      CryptoBulletproofsIPARecursiveTreeGeneratorContract.rate_node_exact]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    cases hh : header src s w with
    | none => simp [rootRate, CryptoBulletproofsIPARecursiveTreeGeneratorContract.rootRate, hh]
    | some p =>
      rcases p with ⟨msg, u⟩
      simp only [rootRate, CryptoBulletproofsIPARecursiveTreeGeneratorContract.rootRate, hh]
      exact Finset.prod_congr rfl (fun i _ => ih (child_statement s msg (u i)))

theorem rate_ge_single (budget : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (hT : ∀ j, 1 ≤ budget (j + 1)) (s : Statement q G k) :
    CryptoBulletproofsIPARecursiveTreeGeneratorContract.rate C src s ≤ rate budget C src s := by
  rw [← rate_single_budget C hC src s]
  exact rate_mono_budget _ _ C hC src hT s

/-- Every valid root must have a zero-rate child to force total failure. -/
theorem rate_zero_of_blocked_child (budget : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (s : Statement q G (k + 1))
    (h : ∀ w ∈ C, ∀ msg u, header src s w = some (msg, u) →
      ∃ i, rate budget C src (child_statement s msg (u i)) = 0) : rate budget C src s = 0 := by
  have hz : attemptRate budget C src s = 0 := by
    rw [attempt_rate_exact]
    suffices ∀ w ∈ C, rootRate budget C src s w = 0 by simp [Finset.sum_eq_zero this]
    intro w hw
    cases hh : header src s w with
    | none => simp [rootRate, hh]
    | some p =>
      rcases p with ⟨msg, u⟩
      obtain ⟨i, hi⟩ := h w hw msg u hh
      simp only [rootRate, hh]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [rate_node_exact budget C hC, hz]
  simp [amplify]

theorem positive_rate_extracts (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G k) (hp : 0 < rate budget C src s) :
    ∃ w ∈ tapes budget C k, ∃ r, extract budget src s w = .ok r ∧ ResultValid s r := by
  rw [rate_probability] at hp
  obtain ⟨w, hw, hg⟩ := positive_probability_has_outcome _ _ hp
  have hs := (Finset.mem_filter.mp hg).2
  cases he : generate budget src s w with
  | none => simp [he] at hs
  | some t =>
    obtain ⟨r, hr⟩ := generated_extracts budget src s w t he
    exact ⟨w, hw, r, hr⟩

theorem dense_extracts (budget : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (a b : ℚ) (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hT : ∀ j, 1 ≤ budget (j + 1)) (s : Statement q G k)
    (h : CryptoBulletproofsIPARecursiveTreeGeneratorContract.Dense C src a b s) :
    ∃ w ∈ tapes budget C k, ∃ r, extract budget src s w = .ok r ∧ ResultValid s r :=
  positive_rate_extracts budget C src s
    (lt_of_lt_of_le (lowerBound_positive budget a b ha ha1 hb hb1 hT k)
      (recursive_probability_lower budget C hC src a b ha.le ha1 hb.le hb1 s h))

/-- Vary only this node's budget, keeping its recursively budgeted child experiment fixed. -/
def localRetryRate (budget : ℕ → ℕ) (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (T : ℕ) : ℚ :=
  probability (productTapes (attemptTapes budget C k) T)
    (successes (productTapes (attemptTapes budget C k) T)
      (tapeAttempt (fun w => (attempt budget src s w).isSome)) T)

theorem local_retry_rate_exact (budget : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (s : Statement q G (k + 1)) (T : ℕ) :
    localRetryRate budget C src s T = amplify (attemptRate budget C src s) T :=
  product_success_probability _ (hC.product (tapes_nonempty budget C hC k).piFinset_const) _ T

/-- Strict growth concerns the actual composed attempt rate, not merely a loose lower bound. -/
theorem local_retry_rate_strict (budget : ℕ → ℕ) (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (s : Statement q G (k + 1))
    (hp : 0 < attemptRate budget C src s) (hp1 : attemptRate budget C src s < 1) :
    StrictMono (localRetryRate budget C src s) := by
  intro i j hij
  rw [local_retry_rate_exact budget C hC, local_retry_rate_exact budget C hC]
  exact amplify_strict_budget _ hp hp1 hij


end Counting

structure CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContractSuite : Prop where
  correctness : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (Ω : Type) (k : ℕ) (budget : ℕ → ℕ) (src : Source q G Ω)
    (s : Statement q G k) (w : Tape budget Ω k) (t : IPATranscriptTree q G k),
      generate budget src s w = some t → ValidAcceptingTree s t
  probability : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (Ω : Type) [DecidableEq Ω] (k : ℕ) (budget : ℕ → ℕ)
    (C : Finset Ω), C.Nonempty → ∀ (src : Source q G Ω) (a b : ℚ),
      0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → ∀ (s : Statement q G k),
      CryptoBulletproofsIPARecursiveTreeGeneratorContract.Dense C src a b s →
        lowerBound budget a b k ≤ rate budget C src s
  extraction : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (Ω : Type) (k : ℕ) (budget : ℕ → ℕ) (src : Source q G Ω)
    (s : Statement q G k) (w : Tape budget Ω k) (r : TreeExtractionResult q k),
      extract budget src s w = .ok r → ResultValid s r

theorem verification_suite : CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContractSuite where
  correctness := fun _ _ _ _ _ _ _ _ => generate_valid
  probability := fun _ _ _ _ _ _ _ _ _ => recursive_probability_lower
  extraction := fun _ _ _ _ _ _ _ _ => extract_sound

end CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract
