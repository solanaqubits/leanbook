/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract

/-! Partial branch caches at a fixed parent fork. Costs count child-generator calls,
not machine time or recursive checks. Both strategies share aligned tape slots. -/
namespace CryptoBulletproofsIPAPartialBranchCacheResourceContract
open scoped BigOperators
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
namespace R
export CryptoBulletproofsIPARecursiveTreeGeneratorContract
  (Source header header_distinct collect collect_some collect_isSome)
end R
namespace N
export CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract (generate generate_valid Tape)
end N

abbrev Cache (α : Type) := Fin 4 → Option α

def emptyCache : Cache α := fun _ => none

def complete (c : Cache α) : Bool := decide (∀ j, (c j).isSome = true)

def missing (c : Cache α) : Finset (Fin 4) := Finset.univ.filter (fun j => (c j).isNone)

/-- The right-hand generator result is used only in an empty slot. -/
def fillMissing (c row : Cache α) : Cache α := fun j =>
  match c j with | some v => some v | none => row j

/-- A round executes exactly the missing slots, keeping their original column indices. -/
def runCache (c : Cache α) : List (Cache α) → Cache α × ℕ
  | [] => (c, 0)
  | row :: rows =>
      let next := runCache (fillMissing c row) rows
      (next.1, (missing c).card + next.2)

/-- Full reset evaluates all four children of every attempted row, even after a failure. -/
def runReset : List (Cache α) → Cache α × ℕ
  | [] => (emptyCache, 0)
  | row :: rows => if complete row then (row, 4)
      else let next := runReset rows; (next.1, 4 + next.2)

theorem complete_iff (c : Cache α) : complete c = true ↔ ∀ j, (c j).isSome = true := by
  simp [complete]

theorem fill_some (c row : Cache α) (j : Fin 4) (v : α) (h : c j = some v) :
    fillMissing c row j = some v := by simp [fillMissing, h]

theorem fill_isSome (c row : Cache α) (j : Fin 4) :
    (fillMissing c row j).isSome = true ↔ (c j).isSome = true ∨ (row j).isSome = true := by
  cases hc : c j <;> simp [fillMissing, hc]

theorem fill_complete_right (c row : Cache α) (h : complete row = true) :
    complete (fillMissing c row) = true := by
  apply (complete_iff _).mpr
  intro j
  exact (fill_isSome c row j).mpr (Or.inr ((complete_iff _).mp h j))

theorem missing_le (c : Cache α) : (missing c).card ≤ 4 := by
  simpa [missing] using Finset.card_filter_le (s := (Finset.univ : Finset (Fin 4)))
    (p := fun j => (c j).isNone = true)

theorem missing_lt_of_some (c : Cache α) (j : Fin 4) (h : (c j).isSome = true) :
    (missing c).card < 4 := by
  have hn : j ∉ missing c := by simp [missing, Option.isNone_iff_eq_none];
                                cases hc : c j <;> simp_all
  have hs : missing c ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ _, fun he => hn (he ▸ Finset.mem_univ j)⟩
  simpa using Finset.card_lt_card hs

theorem runCache_complete (c : Cache α) (rows : List (Cache α)) (h : complete c = true) :
    runCache c rows = (c, 0) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hf : fillMissing c row = c := by
      funext j
      have hj := (complete_iff _).mp h j
      cases hc : c j <;> simp_all [fillMissing]
    have hm : missing c = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j
      have hj := (complete_iff _).mp h j
      cases hc : c j <;> simp_all [missing]
    simp [runCache, hf, hm, ih]

theorem runCache_isSome (c : Cache α) (rows : List (Cache α)) (j : Fin 4) :
    ((runCache c rows).1 j).isSome = true ↔
      (c j).isSome = true ∨ ∃ row ∈ rows, (row j).isSome = true := by
  induction rows generalizing c with
  | nil => simp [runCache]
  | cons row rows ih =>
    simp only [runCache, ih, fill_isSome, List.mem_cons]
    aesop

theorem cache_success_iff (rows : List (Cache α)) :
    complete (runCache emptyCache rows).1 = true ↔
      ∀ j, ∃ row ∈ rows, (row j).isSome = true := by
  simp [complete_iff, runCache_isSome, emptyCache]

theorem reset_success_iff (rows : List (Cache α)) :
    complete (runReset rows).1 = true ↔ ∃ row ∈ rows, complete row = true := by
  induction rows with
  | nil => simp [runReset, complete, emptyCache]
  | cons row rows ih =>
    by_cases h : complete row = true
    · simp [runReset, h]
    · simp [runReset, h, ih]

theorem reset_success_implies_cache (c : Cache α) (rows : List (Cache α))
    (h : complete (runReset rows).1 = true) : complete (runCache c rows).1 = true := by
  obtain ⟨row, hr, hc⟩ := (reset_success_iff rows).mp h
  apply (complete_iff _).mpr
  intro j
  exact (runCache_isSome c rows j).mpr (Or.inr ⟨row, hr, (complete_iff _).mp hc j⟩)

theorem cache_cost_le_reset (c : Cache α) (rows : List (Cache α)) :
    (runCache c rows).2 ≤ (runReset rows).2 := by
  induction rows generalizing c with
  | nil => simp [runCache, runReset]
  | cons row rows ih =>
    by_cases h : complete row = true
    · have ht := runCache_complete (fillMissing c row) rows (fill_complete_right c row h)
      simpa [runCache, runReset, h, ht] using missing_le c
    · simpa [runCache, runReset, h] using Nat.add_le_add (missing_le c) (ih (fillMissing c row))

theorem reset_cost_le_budget (rows : List (Cache α)) :
    (runReset rows).2 ≤ 4 * rows.length := by
  induction rows with
  | nil => simp [runReset]
  | cons row rows ih =>
    by_cases h : complete row = true
    · simp [runReset, h]
    · simp [runReset, h]
      omega

theorem cache_cost_le_budget (c : Cache α) (rows : List (Cache α)) :
    (runCache c rows).2 ≤ 4 * rows.length :=
  (cache_cost_le_reset c rows).trans (reset_cost_le_budget rows)

/-- Strict saving needs an executed round containing an already-filled column. -/
theorem cache_cost_lt_reset_of_filled (c row : Cache α) (rows : List (Cache α))
    (j : Fin 4) (h : (c j).isSome = true) :
    (runCache c (row :: rows)).2 < (runReset (row :: rows)).2 := by
  have hm := missing_lt_of_some c j h
  by_cases hr : complete row = true
  · have ht := runCache_complete (fillMissing c row) rows (fill_complete_right c row hr)
    simpa [runCache, runReset, hr, ht] using hm
  · have ht := cache_cost_le_reset (fillMissing c row) rows
    simp [runCache, runReset, hr]
    omega

/-- A partial success saves calls only if a subsequent round is available. -/
theorem strict_saving_after_partial (row next : Cache α) (rows : List (Cache α))
    (hn : complete row = false) (j : Fin 4) (hj : (row j).isSome = true) :
    (runCache emptyCache (row :: next :: rows)).2 <
      (runReset (row :: next :: rows)).2 := by
  have ht := cache_cost_lt_reset_of_filled row next rows j hj
  have he : fillMissing (emptyCache : Cache α) row = row := by
    funext j; simp [fillMissing, emptyCache]
  simpa only [runCache, runReset, hn, Bool.false_eq_true, ↓reduceIte, he, Prod.snd,
    missing, emptyCache, Option.isNone_none, Finset.filter_true, Finset.card_univ,
    Fintype.card_fin] using
    Nat.add_lt_add_left ht (missing (emptyCache : Cache α)).card

def missingList (c : Cache α) : List (Fin 4) :=
  (List.finRange 4).filter (fun j => (c j).isNone)

theorem missingList_length (c : Cache α) : (missingList c).length = (missing c).card := by
  have he : (missingList c).toFinset = missing c := by ext j; simp [missingList, missing]
  rw [← he, List.toFinset_card_of_nodup]
  exact (List.nodup_finRange 4).filter _

/-- Explicit scheduled child calls. Every skipped filled slot is absent from this trace. -/
def cacheTrace (c : Cache α) : List (Cache α) → List (ℕ × Fin 4)
  | [] => []
  | row :: rows => (missingList c).map (fun j => (0, j)) ++
      (cacheTrace (fillMissing c row) rows).map (fun p => (p.1 + 1, p.2))

def resetTrace : List (Cache α) → List (ℕ × Fin 4)
  | [] => []
  | row :: rows => (List.finRange 4).map (fun j => (0, j)) ++
      if complete row then [] else (resetTrace rows).map (fun p => (p.1 + 1, p.2))

theorem cacheTrace_length (c : Cache α) (rows : List (Cache α)) :
    (cacheTrace c rows).length = (runCache c rows).2 := by
  induction rows generalizing c with
  | nil => rfl
  | cons row rows ih => simp [cacheTrace, runCache, ih, missingList_length]

theorem resetTrace_length (rows : List (Cache α)) :
    (resetTrace rows).length = (runReset rows).2 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases h : complete row = true <;> simp [resetTrace, runReset, h, ih]

theorem cacheTrace_complete (c : Cache α) (rows : List (Cache α))
    (h : complete c = true) : cacheTrace c rows = [] := by
  apply List.length_eq_zero_iff.mp
  rw [cacheTrace_length, runCache_complete c rows h]

theorem cacheTrace_subset_reset (c : Cache α) (rows : List (Cache α)) :
    ∀ p ∈ cacheTrace c rows, p ∈ resetTrace rows := by
  induction rows generalizing c with
  | nil => simp [cacheTrace]
  | cons row rows ih =>
    intro p hp
    simp only [cacheTrace, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨j, _, rfl⟩ | ⟨v, hv, rfl⟩
    · apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨j, List.mem_finRange j, rfl⟩
    · by_cases h : complete row = true
      · rw [cacheTrace_complete _ _ (fill_complete_right c row h)] at hv
        simp at hv
      · simp only [resetTrace, h, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_map]
        exact Or.inr ⟨v, ih (fillMissing c row) v hv, rfl⟩

section Context
variable {q : ℕ} [Fact q.Prime] {G : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] {k : ℕ}

omit [DecidableEq G] in
/-- The unchanged tree stores one claimed root statement; validity fixes its context. -/
theorem valid_tree_context_unique (s s' : Statement q G k) (t : IPATranscriptTree q G k)
    (h : ValidAcceptingTree s t) (h' : ValidAcceptingTree s' t) : s = s' := by
  cases t with
  | leaf c a b => exact h.1.symm.trans h'.1
  | node c msg u ts => exact h.1.symm.trans h'.1

omit [DecidableEq G] in
theorem valid_tree_transfer_iff (old new : Statement q G k) (t : IPATranscriptTree q G k)
    (h : ValidAcceptingTree old t) : ValidAcceptingTree new t ↔ new = old := by
  constructor
  · intro hn; exact (valid_tree_context_unique old new t h hn).symm
  · intro he; simpa [he] using h

/-- Transfer preserves the original tree; validity of that tree is a separate invariant. -/
def checkedTransfer (old new : Statement q G k) (t : IPATranscriptTree q G k) :
    Option (IPATranscriptTree q G k) := if new = old then some t else none

theorem checkedTransfer_valid (old new : Statement q G k) (t : IPATranscriptTree q G k)
    (h : ValidAcceptingTree old t) :
    checkedTransfer old new t = some t ↔ ValidAcceptingTree new t := by
  rw [valid_tree_transfer_iff old new t h]
  simp [checkedTransfer]

structure FixedFork (q : ℕ) (G : Type) (k : ℕ) where
  parent : Statement q G (k + 1)
  msg : RoundMessages G
  u : Fin 4 → (ZMod q)ˣ
  distinct : Function.Injective (fun j => (u j : ZMod q) ^ 2)

def childContext (F : FixedFork q G k) (j : Fin 4) : Statement q G k :=
  child_statement F.parent F.msg (F.u j)

/-- Empty slots inherit their key from the fixed fork; occupied slots must validate at that key. -/
def CacheValid (F : FixedFork q G k) (c : Cache (IPATranscriptTree q G k)) : Prop :=
  ∀ j t, c j = some t → ValidAcceptingTree (childContext F j) t

omit [DecidableEq G] in
theorem empty_valid (F : FixedFork q G k) : CacheValid F emptyCache := by
  intro j t h; simp [emptyCache] at h

omit [DecidableEq G] in
theorem fill_valid (F : FixedFork q G k) (c row : Cache (IPATranscriptTree q G k))
    (hc : CacheValid F c) (hr : CacheValid F row) : CacheValid F (fillMissing c row) := by
  intro j t ht
  cases hj : c j with
  | none => exact hr j t (by simpa [fillMissing, hj] using ht)
  | some v => have he : v = t := by simpa [fillMissing, hj] using ht
              subst v
              exact hc j t hj

omit [DecidableEq G] in
theorem runCache_valid (F : FixedFork q G k) (c : Cache (IPATranscriptTree q G k))
    (rows : List (Cache (IPATranscriptTree q G k))) (hc : CacheValid F c)
    (hr : ∀ row ∈ rows, CacheValid F row) : CacheValid F (runCache c rows).1 := by
  induction rows generalizing c with
  | nil => exact hc
  | cons row rows ih =>
    exact ih (fillMissing c row) (fill_valid F c row hc (hr row (by simp)))
      (fun r h => hr r (by simp [h]))

def assemble (F : FixedFork q G k) (c : Cache (IPATranscriptTree q G k)) :
    Option (IPATranscriptTree q G (k + 1)) :=
  (R.collect c).map (fun ts => .node F.parent F.msg (fun j => F.u j) ts)

omit [DecidableEq G] in
theorem assemble_valid (F : FixedFork q G k) (c : Cache (IPATranscriptTree q G k))
    (hc : CacheValid F c) (t : IPATranscriptTree q G (k + 1)) (ht : assemble F c = some t) :
    ValidAcceptingTree F.parent t := by
  obtain ⟨ts, hs, he⟩ := Option.map_eq_some_iff.mp ht
  cases he
  refine ⟨rfl, ?_⟩
  rw [dif_pos (fun j => Units.ne_zero (F.u j))]
  refine ⟨F.distinct, ?_⟩
  intro j
  simpa only [Units.mk0_val, childContext] using hc j (ts j) ((R.collect_some _ _).mp hs j)

omit [Fact q.Prime] [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G] in
theorem assemble_isSome (F : FixedFork q G k) (c : Cache (IPATranscriptTree q G k)) :
    (assemble F c).isSome = true ↔ complete c = true := by
  simp [assemble, R.collect_isSome, complete_iff]

/-- Concrete row outcomes use the existing recursive node-local generator at computed contexts. -/
def childRows {Ω : Type} (F : FixedFork q G k) (budget : ℕ → ℕ) (src : R.Source q G Ω)
    (tapes : List (Fin 4 → N.Tape budget Ω k)) : List (Cache (IPATranscriptTree q G k)) :=
  tapes.map (fun row j => N.generate budget src (childContext F j) (row j))

theorem childRows_valid {Ω : Type} (F : FixedFork q G k) (budget : ℕ → ℕ) (src : R.Source q G Ω)
    (tapes : List (Fin 4 → N.Tape budget Ω k)) :
    ∀ row ∈ childRows F budget src tapes, CacheValid F row := by
  intro row hr
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hr
  intro j t ht
  exact N.generate_valid budget src (childContext F j) (w j) t ht

def cachedGenerate {Ω : Type} (F : FixedFork q G k) (budget : ℕ → ℕ) (src : R.Source q G Ω)
    (tapes : List (Fin 4 → N.Tape budget Ω k)) : Option (IPATranscriptTree q G (k + 1)) :=
  assemble F (runCache emptyCache (childRows F budget src tapes)).1

theorem cachedGenerate_valid {Ω : Type} (F : FixedFork q G k) (budget : ℕ → ℕ)
    (src : R.Source q G Ω) (tapes : List (Fin 4 → N.Tape budget Ω k))
    (t : IPATranscriptTree q G (k + 1)) (h : cachedGenerate F budget src tapes = some t) :
    ValidAcceptingTree F.parent t :=
  assemble_valid F _ (runCache_valid F _ _ (empty_valid F) (childRows_valid F budget src tapes)) t h

theorem cachedGenerate_extracts {Ω : Type} (F : FixedFork q G k) (budget : ℕ → ℕ)
    (src : R.Source q G Ω) (tapes : List (Fin 4 → N.Tape budget Ω k))
    (t : IPATranscriptTree q G (k + 1)) (h : cachedGenerate F budget src tapes = some t) :
    checked_extract F.parent t = .ok (extractTree t) ∧ ResultValid F.parent (extractTree t) := by
  have hv := cachedGenerate_valid F budget src tapes t h
  exact ⟨by simp [checked_extract, hv], tree_extraction_soundness F.parent t hv⟩

theorem cachedGenerate_success_iff {Ω : Type} (F : FixedFork q G k) (budget : ℕ → ℕ)
    (src : R.Source q G Ω) (tapes : List (Fin 4 → N.Tape budget Ω k)) :
    (cachedGenerate F budget src tapes).isSome = true ↔
      ∀ j, ∃ row ∈ tapes, (N.generate budget src (childContext F j) (row j)).isSome = true := by
  rw [cachedGenerate, assemble_isSome, cache_success_iff]
  simp [childRows]

/-- Rejecting a header performs no child-generator calls in either strategy. -/
def checkedCachedNode {Ω : Type} (budget : ℕ → ℕ) (src : R.Source q G Ω)
    (s : Statement q G (k + 1)) (w : Ω) (tapes : List (Fin 4 → N.Tape budget Ω k)) :
    Option (IPATranscriptTree q G (k + 1)) × ℕ :=
  match hh : R.header src s w with
  | none => (none, 0)
  | some (msg, u) =>
      let F : FixedFork q G k := ⟨s, msg, u, R.header_distinct src s w msg u hh⟩
      let result := runCache emptyCache (childRows F budget src tapes)
      (assemble F result.1, result.2)

theorem invalid_header_no_calls {Ω : Type} (budget : ℕ → ℕ) (src : R.Source q G Ω)
    (s : Statement q G (k + 1)) (w : Ω) (tapes : List (Fin 4 → N.Tape budget Ω k))
    (h : R.header src s w = none) : checkedCachedNode budget src s w tapes = (none, 0) := by
  unfold checkedCachedNode
  split
  · rfl
  · rename_i msg u hh
    simp [h] at hh
end Context

open CryptoBulletproofsIPAProductTapeCandidateGeneratorContract
open CryptoBulletproofsIPABoundedRetryContract
open CryptoBulletproofsIPATreeProbabilityContract

section Probability
variable {Ω : Type}

def branchSpace (C : Fin 4 → Finset Ω) (R : ℕ) : Finset (Fin 4 → Fin R → Ω) :=
  Fintype.piFinset (fun j => productTapes (C j) R)

def cacheEvent (R : ℕ) (a : Fin 4 → Ω → Bool) (w : Fin 4 → Fin R → Ω) : Bool :=
  decide (∀ j, ∃ r, a j (w j r) = true)

def resetEvent (R : ℕ) (a : Fin 4 → Ω → Bool) (w : Fin 4 → Fin R → Ω) : Bool :=
  decide (∃ r, ∀ j, a j (w j r) = true)

theorem reset_event_implies_cache (R : ℕ) (a : Fin 4 → Ω → Bool)
    (w : Fin 4 → Fin R → Ω) (h : resetEvent R a w = true) : cacheEvent R a w = true := by
  simp only [resetEvent, decide_eq_true_eq] at h
  simp only [cacheEvent, decide_eq_true_eq]
  obtain ⟨r, hr⟩ := h
  exact fun j => ⟨r, hr j⟩

theorem cache_probability_dominates (R : ℕ) (a : Fin 4 → Ω → Bool)
    (D : Finset (Fin 4 → Fin R → Ω)) :
    singleProbability D (resetEvent R a) ≤ singleProbability D (cacheEvent R a) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show goodTapes D (resetEvent R a) ⊆
      goodTapes D (cacheEvent R a) from by
    intro w hw
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
      reset_event_implies_cache R a w (Finset.mem_filter.mp hw).2⟩)

theorem independent_all_probability {I : Type} [Fintype I] [DecidableEq I]
    (C : I → Finset Ω) (a : I → Ω → Bool) :
    singleProbability (Fintype.piFinset C) (fun w => decide (∀ j, a j (w j) = true)) =
      ∏ j, singleProbability (C j) (a j) := by
  have he : goodTapes (Fintype.piFinset C) (fun w => decide (∀ j, a j (w j) = true)) =
      Fintype.piFinset (fun j => goodTapes (C j) (a j)) := by
    ext w
    simp only [goodTapes, Finset.mem_filter, Fintype.mem_piFinset, decide_eq_true_eq]
    exact forall_and.symm
  rw [singleProbability, he, Fintype.card_piFinset, Fintype.card_piFinset]
  simp only [Nat.cast_prod, Finset.prod_div_distrib, singleProbability]

theorem independent_any_probability (C : Finset Ω) (hC : C.Nonempty)
    (a : Ω → Bool) (R : ℕ) :
    singleProbability (productTapes C R) (fun w => decide (∃ r, a (w r) = true)) =
      1 - (1 - singleProbability C a)^R := by
  classical
  have he : goodTapes (productTapes C R) (fun w => decide (∃ r, a (w r) = true)) =
      successes (productTapes C R) (tapeAttempt a) R := by
    ext w
    simp only [goodTapes, successes, Finset.mem_filter, decide_eq_true_eq, ne_eq, firstSuccess_none]
    apply and_congr_right
    intro _
    simp only [not_forall, Bool.not_eq_false]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r.val, r.isLt, by simpa [tapeAttempt, r.isLt] using hr⟩
    · rintro ⟨i, hi, ha⟩
      exact ⟨⟨i, hi⟩, by simpa [tapeAttempt, hi] using ha⟩
  have hp := product_success_probability C hC a R
  rw [probability, Finset.inter_eq_left.mpr (show
    successes (productTapes C R) (tapeAttempt a) R ⊆ productTapes C R
      from Finset.filter_subset _ _)] at hp
  simpa only [singleProbability, he] using hp

theorem cache_probability_exact (C : Fin 4 → Finset Ω) (hC : ∀ j, (C j).Nonempty)
    (a : Fin 4 → Ω → Bool) (R : ℕ) :
    singleProbability (branchSpace C R) (cacheEvent R a) =
      ∏ j, (1 - (1 - singleProbability (C j) (a j))^R) := by
  calc
    _ = ∏ j, singleProbability (productTapes (C j) R)
        (fun w => decide (∃ r, a j (w r) = true)) := by
      unfold branchSpace cacheEvent
      simpa only [decide_eq_true_eq] using
        independent_all_probability (fun j => productTapes (C j) R)
          (fun j w => decide (∃ r, a j (w r) = true))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      exact independent_any_probability (C j) (hC j) (a j) R

/-- Transposition identifies independently sampled columns with independently sampled rows. -/
theorem transpose_space (C : Fin 4 → Finset Ω) (R : ℕ) :
    (branchSpace C R).map (Equiv.piComm (fun (_ : Fin 4) (_ : Fin R) => Ω)).toEmbedding =
      productTapes (Fintype.piFinset C) R := by
  ext w
  simp only [Finset.mem_map, branchSpace, productTapes, Fintype.mem_piFinset,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact fun r j => hv j r
  · intro hw
    exact ⟨fun j r => w r j, fun j r => hw r j, rfl⟩

theorem transpose_good (C : Fin 4 → Finset Ω) (a : Fin 4 → Ω → Bool) (R : ℕ) :
    (goodTapes (branchSpace C R) (resetEvent R a)).map
        (Equiv.piComm (fun (_ : Fin 4) (_ : Fin R) => Ω)).toEmbedding =
      goodTapes (productTapes (Fintype.piFinset C) R)
        (fun w => decide (∃ r, ∀ j, a j (w r j) = true)) := by
  ext w
  simp only [Finset.mem_map, goodTapes, Finset.mem_filter, branchSpace, productTapes,
    Fintype.mem_piFinset, resetEvent, decide_eq_true_eq, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨v, ⟨hv, ha⟩, rfl⟩
    exact ⟨fun r j => hv j r, ha⟩
  · rintro ⟨hw, ha⟩
    exact ⟨fun j r => w r j, ⟨fun j r => hw r j, ha⟩, rfl⟩

theorem reset_probability_exact (C : Fin 4 → Finset Ω) (hC : ∀ j, (C j).Nonempty)
    (a : Fin 4 → Ω → Bool) (R : ℕ) :
    singleProbability (branchSpace C R) (resetEvent R a) =
      1 - (1 - ∏ j, singleProbability (C j) (a j))^R := by
  have hc := congrArg Finset.card (transpose_space C R)
  have hg := congrArg Finset.card (transpose_good C a R)
  simp only [Finset.card_map] at hc hg
  have hp := independent_any_probability (Fintype.piFinset C)
    (Fintype.piFinset_nonempty.mpr hC) (fun w => decide (∀ j, a j (w j) = true)) R
  have hall := independent_all_probability C a
  simp only [singleProbability, goodTapes, decide_eq_true_eq] at hall hp
  rw [hall] at hp
  unfold singleProbability
  rw [hc, hg]
  simpa only [goodTapes, decide_eq_true_eq] using hp

theorem independent_cache_dominates_reset (C : Fin 4 → Finset Ω)
    (hC : ∀ j, (C j).Nonempty) (a : Fin 4 → Ω → Bool) (R : ℕ) :
    1 - (1 - ∏ j, singleProbability (C j) (a j))^R ≤
      ∏ j, (1 - (1 - singleProbability (C j) (a j))^R) := by
  rw [← reset_probability_exact C hC a R, ← cache_probability_exact C hC a R]
  exact cache_probability_dominates R a (branchSpace C R)

end Probability

section ExecutionProbability
variable {Ω α : Type}

def tableRows {R : ℕ} (f : Fin 4 → Ω → Option α) (w : Fin 4 → Fin R → Ω) :
    List (Cache α) := List.ofFn (fun r j => f j (w j r))

theorem cache_run_event {R : ℕ} (f : Fin 4 → Ω → Option α) (w : Fin 4 → Fin R → Ω) :
    complete (runCache emptyCache (tableRows f w)).1 =
      cacheEvent R (fun j ω => (f j ω).isSome) w := by
  apply Bool.eq_iff_iff.mpr
  rw [cache_success_iff]
  simp [tableRows, cacheEvent]

theorem reset_run_event {R : ℕ} (f : Fin 4 → Ω → Option α) (w : Fin 4 → Fin R → Ω) :
    complete (runReset (tableRows f w)).1 = resetEvent R (fun j ω => (f j ω).isSome) w := by
  apply Bool.eq_iff_iff.mpr
  rw [reset_success_iff]
  simp [tableRows, resetEvent, complete_iff]

/-- Pointwise resource domination gives mean call domination for any finite table population. -/
theorem mean_cache_cost_le_reset {R : ℕ} (f : Fin 4 → Ω → Option α)
    (D : Finset (Fin 4 → Fin R → Ω)) :
    (∑ w ∈ D, ((runCache emptyCache (tableRows f w)).2 : ℚ)) / D.card ≤
      (∑ w ∈ D, ((runReset (tableRows f w)).2 : ℚ)) / D.card := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro w _
  exact_mod_cast cache_cost_le_reset emptyCache (tableRows f w)


theorem cache_run_probability_exact (C : Fin 4 → Finset Ω) (hC : ∀ j, (C j).Nonempty)
    (f : Fin 4 → Ω → Option α) (R : ℕ) :
    singleProbability (branchSpace C R)
      (fun w => complete (runCache emptyCache (tableRows f w)).1) =
      ∏ j, (1 - (1 - singleProbability (C j) (fun ω => (f j ω).isSome))^R) := by
  simp_rw [cache_run_event]
  exact cache_probability_exact C hC _ R

theorem reset_run_probability_exact (C : Fin 4 → Finset Ω) (hC : ∀ j, (C j).Nonempty)
    (f : Fin 4 → Ω → Option α) (R : ℕ) :
    singleProbability (branchSpace C R) (fun w => complete (runReset (tableRows f w)).1) =
      1 - (1 - ∏ j, singleProbability (C j) (fun ω => (f j ω).isSome))^R := by
  simp_rw [reset_run_event]
  exact reset_probability_exact C hC _ R
end ExecutionProbability

section GeneratorProbability
variable {q : ℕ} [Fact q.Prime] {G : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] {k : ℕ} {Ω : Type}

theorem cachedGenerate_table_event (F : FixedFork q G k) (budget : ℕ → ℕ)
    (src : R.Source q G Ω) {R : ℕ} (w : Fin 4 → Fin R → N.Tape budget Ω k) :
    (cachedGenerate F budget src (List.ofFn (fun r j => w j r))).isSome =
      cacheEvent R (fun j ω => (N.generate budget src (childContext F j) ω).isSome) w := by
  apply Bool.eq_iff_iff.mpr
  rw [cachedGenerate_success_iff]
  simp [cacheEvent]

/-- The exact formula applies to the actual ε209 child generator, including its inner budgets. -/
theorem cachedGenerate_probability_exact (F : FixedFork q G k) (budget : ℕ → ℕ)
    (src : R.Source q G Ω)
    (C : Fin 4 → Finset (N.Tape budget Ω k)) (hC : ∀ j, (C j).Nonempty) (R : ℕ) :
    singleProbability (branchSpace C R)
      (fun w => (cachedGenerate F budget src (List.ofFn (fun r j => w j r))).isSome) =
      ∏ j, (1 - (1 - singleProbability (C j)
        (fun ω => (N.generate budget src (childContext F j) ω).isSome))^R) := by
  simp_rw [cachedGenerate_table_event]
  exact cache_probability_exact C hC _ R
end GeneratorProbability


/-- Filled values, not just their success flags, survive every subsequent round. -/
theorem runCache_preserves (c : Cache α) (rows : List (Cache α)) (j : Fin 4) (v : α)
    (h : c j = some v) : (runCache c rows).1 j = some v := by
  induction rows generalizing c with
  | nil => exact h
  | cons row rows ih => exact ih (fillMissing c row) (fill_some c row j v h)

structure CryptoBulletproofsIPAPartialBranchCacheResourceContractSuite : Prop where
  context : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    (k : ℕ) (old new : Statement q G k) (t : IPATranscriptTree q G k),
      ValidAcceptingTree old t → (ValidAcceptingTree new t ↔ new = old)
  resource : ∀ (α : Type) (c : Cache α) (rows : List (Cache α)),
    (runCache c rows).2 ≤ (runReset rows).2
  trace : ∀ (α : Type) (c : Cache α) (rows : List (Cache α)),
    (cacheTrace c rows).length = (runCache c rows).2 ∧
      ∀ p ∈ cacheTrace c rows, p ∈ resetTrace rows
  success : ∀ (α : Type) (c : Cache α) (rows : List (Cache α)),
    complete (runReset rows).1 = true → complete (runCache c rows).1 = true
  probability : ∀ (Ω α : Type) (C : Fin 4 → Finset Ω),
    (∀ j, (C j).Nonempty) → ∀ (f : Fin 4 → Ω → Option α) (R : ℕ),
    singleProbability (branchSpace C R)
      (fun w => complete (runCache emptyCache (tableRows f w)).1) =
      ∏ j, (1 - (1 - singleProbability (C j) (fun ω => (f j ω).isSome))^R)
  resetProbability : ∀ (Ω α : Type) (C : Fin 4 → Finset Ω),
    (∀ j, (C j).Nonempty) → ∀ (f : Fin 4 → Ω → Option α) (R : ℕ),
    singleProbability (branchSpace C R) (fun w => complete (runReset (tableRows f w)).1) =
      1 - (1 - ∏ j, singleProbability (C j) (fun ω => (f j ω).isSome))^R
  extraction : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (Ω : Type) (k : ℕ) (F : FixedFork q G k) (budget : ℕ → ℕ)
    (src : R.Source q G Ω) (tapes : List (Fin 4 → N.Tape budget Ω k))
    (t : IPATranscriptTree q G (k + 1)), cachedGenerate F budget src tapes = some t →
      checked_extract F.parent t = .ok (extractTree t) ∧ ResultValid F.parent (extractTree t)

theorem verification_suite : CryptoBulletproofsIPAPartialBranchCacheResourceContractSuite where
  context := fun _ _ _ _ _ _ => valid_tree_transfer_iff
  resource := fun _ => cache_cost_le_reset
  trace := fun _ c rows => ⟨cacheTrace_length c rows, cacheTrace_subset_reset c rows⟩
  success := fun _ => reset_success_implies_cache
  probability := fun _ _ => cache_run_probability_exact
  resetProbability := fun _ _ => reset_run_probability_exact
  extraction := fun _ _ _ _ _ _ _ _ => cachedGenerate_extracts

end CryptoBulletproofsIPAPartialBranchCacheResourceContract
