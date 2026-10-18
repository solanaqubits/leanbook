/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAProductTapeCandidateGeneratorContract

/-! Recursive generation from explicit messages and scalar proposals. Separate finite
coordinates do not imply availability of accepting responses. No ROM or runtime claim. -/
namespace CryptoBulletproofsIPARecursiveTreeGeneratorContract
open scoped BigOperators
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
open CryptoBulletproofsIPATreeProbabilityContract

/-- One local seed at each internal node and leaf. -/
def Tape (Ω : Type) : ℕ → Type
  | 0 => Ω
  | k + 1 => Ω × (Fin 4 → Tape Ω k)

instance tapeDecidableEq {Ω : Type} [DecidableEq Ω] (k : ℕ) : DecidableEq (Tape Ω k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq Ω)
  | succ k ih => exact inferInstanceAs (DecidableEq (Ω × (Fin 4 → Tape Ω k)))

/-- Uniform independent local seeds, including seeds for scalar leaves. -/
def tapes {Ω : Type} [DecidableEq Ω] (C : Finset Ω) : (k : ℕ) → Finset (Tape Ω k)
  | 0 => C
  | k + 1 => C ×ˢ Fintype.piFinset (fun _ : Fin 4 => tapes C k)

theorem tapes_card {Ω : Type} [DecidableEq Ω] (C : Finset Ω) (k : ℕ) :
    (tapes C k).card = C.card ^ checkCount k := by
  induction k with
  | zero => exact (pow_one C.card).symm
  | succ k ih =>
    change (C ×ˢ Fintype.piFinset (fun _ : Fin 4 => tapes C k)).card = _
    rw [Finset.card_product, Fintype.card_piFinset_const, ih]
    simp [checkCount, pow_add, pow_mul, mul_comm]

variable {q : ℕ} [Fact q.Prime] {G : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] {Ω : Type} {k : ℕ}

/-- These are proposals, not certificates of validity or supplied completed trees. -/
structure Source (q : ℕ) (G Ω : Type) where
  leaf : Statement q G 0 → Ω → Option (Statement q G 0 × ZMod q × ZMod q)
  node : (k : ℕ) → Statement q G (k + 1) → Ω →
    Option (Statement q G (k + 1) × RoundMessages G × (Fin 4 → ZMod q))

/-- Validate the claimed context, common prefix and four challenges before recursion. -/
def header (src : Source q G Ω) (s : Statement q G (k + 1)) (w : Ω) :
    Option (RoundMessages G × (Fin 4 → (ZMod q)ˣ)) :=
  match src.node k s w with
  | none => none
  | some (c, msg, u) =>
    if c = s then
      if hn : ∀ i, u i ≠ 0 then
        if Function.Injective (fun i => u i ^ 2)
        then some (msg, fun i => Units.mk0 (u i) (hn i)) else none
      else none
    else none

omit [AddCommGroup G] [Module (ZMod q) G] in
theorem header_distinct (src : Source q G Ω) (s : Statement q G (k + 1)) (w : Ω)
    (msg : RoundMessages G) (u : Fin 4 → (ZMod q)ˣ) (h : header src s w = some (msg, u)) :
    Function.Injective (fun i => (u i : ZMod q) ^ 2) := by
  unfold header at h
  split at h
  · contradiction
  · split_ifs at h with hc hn hd
    · cases Option.some.inj h
      exact hd

/-- No default child is manufactured for a missing response. -/
def collect {α : Type} (f : Fin 4 → Option α) : Option (Fin 4 → α) :=
  if h : ∀ i, (f i).isSome = true then some (fun i => (f i).get (h i)) else none

theorem collect_some {α : Type} (f : Fin 4 → Option α) (v : Fin 4 → α) :
    collect f = some v ↔ ∀ i, f i = some (v i) := by
  unfold collect
  split_ifs with h
  · constructor
    · intro he
      cases Option.some.inj he
      intro i
      exact (Option.some_get (h i)).symm
    · intro hv
      congr 1
      funext i
      simp [hv i]
  · constructor
    · simp
    · intro hv
      exact False.elim (h (fun i => by simp [hv i]))

theorem collect_isSome {α : Type} (f : Fin 4 → Option α) :
    (collect f).isSome = true ↔ ∀ i, (f i).isSome = true := by
  simp [collect]

/-- Actual recursive computation, checking each leaf against its computed context. -/
def generate (src : Source q G Ω) : {k : ℕ} → Statement q G k → Tape Ω k →
    Option (IPATranscriptTree q G k)
  | 0, s, w =>
    match src.leaf s w with
    | none => none
    | some (c, a, b) =>
      if c = s ∧ s.P = a • s.G 0 + b • s.H 0 + (a * b) • s.U
      then some (.leaf c a b) else none
  | _ + 1, s, w =>
    match header src s w.1 with
    | none => none
    | some (msg, u) =>
      (collect (fun i => generate src (child_statement s msg (u i)) (w.2 i))).map
        (fun ts => .node s msg (fun i => u i) ts)

theorem generate_valid (src : Source q G Ω) (s : Statement q G k) (w : Tape Ω k)
    (t : IPATranscriptTree q G k) (h : generate src s w = some t) :
    ValidAcceptingTree s t := by
  induction k with
  | zero =>
    simp only [generate] at h
    split at h
    · contradiction
    · split at h
      · cases Option.some.inj h
        assumption
      · contradiction
  | succ k ih =>
    simp only [generate] at h
    split at h
    · contradiction
    · rename_i msg u hh
      obtain ⟨ts, ht, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      refine ⟨rfl, ?_⟩
      rw [dif_pos (fun i => Units.ne_zero (u i))]
      refine ⟨header_distinct src s w.1 msg u hh, ?_⟩
      intro i
      simpa only [Units.mk0_val] using ih _ _ _ ((collect_some _ _).mp ht i)

/-- All supplied responses in a selected branch are required. -/
theorem generate_node_event (src : Source q G Ω) (s : Statement q G (k + 1))
    (w : Tape Ω (k + 1)) :
    (generate src s w).isSome = true ↔
      ∃ msg u, header src s w.1 = some (msg, u) ∧
        ∀ i, (generate src (child_statement s msg (u i)) (w.2 i)).isSome = true := by
  simp only [generate]
  cases hh : header src s w.1 with
  | none => simp
  | some p => rcases p with ⟨msg, u⟩; simp [collect_isSome]

def extract (src : Source q G Ω) (s : Statement q G k) (w : Tape Ω k) :
    Except String (TreeExtractionResult q k) :=
  match generate src s w with
  | none => .error "recursiveCandidateUnavailable"
  | some t => checked_extract s t

theorem generated_extracts (src : Source q G Ω) (s : Statement q G k) (w : Tape Ω k)
    (t : IPATranscriptTree q G k) (h : generate src s w = some t) :
    ∃ r, extract src s w = .ok r ∧ ResultValid s r := by
  have hv := generate_valid src s w t h
  exact ⟨extractTree t, by simp [extract, h, checked_extract, hv],
    tree_extraction_soundness s t hv⟩

theorem extract_sound (src : Source q G Ω) (s : Statement q G k) (w : Tape Ω k)
    (r : TreeExtractionResult q k) (h : extract src s w = .ok r) : ResultValid s r := by
  unfold extract at h
  split at h
  · contradiction
  · exact checked_extract_sound _ _ _ h

theorem extract_event (src : Source q G Ω) (s : Statement q G k) (w : Tape Ω k) :
    (extract src s w).isOk = true ↔ (generate src s w).isSome = true := by
  cases h : generate src s w with
  | none => simp [extract, h, Except.isOk, Except.toBool]
  | some t =>
    have hv := generate_valid src s w t h
    simp [extract, h, checked_extract, hv, Except.isOk, Except.toBool]


section Counting
variable [DecidableEq Ω]

/-- Successful complete tapes, not merely successful root challenges. -/
def good (C : Finset Ω) (src : Source q G Ω) (s : Statement q G k) : Finset (Tape Ω k) :=
  (tapes C k).filter (fun w => (generate src s w).isSome = true)

def rate (C : Finset Ω) (src : Source q G Ω) (s : Statement q G k) : ℚ :=
  (good C src s).card / ((tapes C k).card : ℚ)

theorem rate_probability (C : Finset Ω) (src : Source q G Ω) (s : Statement q G k) :
    rate C src s = probability (tapes C k) (good C src s) := by
  simp [probability, rate, good, Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]

theorem rate_nonnegative (C : Finset Ω) (src : Source q G Ω) (s : Statement q G k) :
    0 ≤ rate C src s := by unfold rate; positivity

/-- Fixing the root seed fixes all four child contexts. Only then do their counts factor. -/
def rootCount (C : Finset Ω) (src : Source q G Ω) (s : Statement q G (k + 1)) (w : Ω) : ℕ :=
  match header src s w with
  | none => 0
  | some (msg, u) => ∏ i, (good C src (child_statement s msg (u i))).card

omit [DecidableEq Ω] in
theorem branch_filter (D : Finset (Tape Ω k)) (f : Fin 4 → Tape Ω k → Bool) :
    (Fintype.piFinset (fun _ : Fin 4 => D)).filter (fun v => ∀ i, f i (v i) = true) =
      Fintype.piFinset (fun i => D.filter (fun t => f i t = true)) := by
  ext v
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

theorem fixed_root_count (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (w : Ω) :
    ((Fintype.piFinset (fun _ : Fin 4 => tapes C k)).filter
      (fun v => (generate src s (w, v)).isSome = true)).card = rootCount C src s w := by
  cases hh : header src s w with
  | none => simp [generate, hh, rootCount]
  | some p =>
    rcases p with ⟨msg, u⟩
    simp only [generate, hh, Option.isSome_map, collect_isSome, rootCount]
    rw [branch_filter (Ω := Ω) (k := k) (tapes C k)
      (fun i t => (generate src (child_statement s msg (u i)) t).isSome),
      Fintype.card_piFinset]
    rfl

theorem good_node_count (C : Finset Ω) (src : Source q G Ω) (s : Statement q G (k + 1)) :
    (good C src s).card = ∑ w ∈ C, rootCount C src s w := by
  change ((C ×ˢ Fintype.piFinset (fun _ : Fin 4 => tapes C k)).filter
    (fun w : Ω × (Fin 4 → Tape Ω k) => (generate src s w).isSome = true)).card = _
  simp only [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w _
  simpa only [Finset.card_filter] using fixed_root_count C src s w

/-- A conditional child probability given this exact root seed/context. -/
def rootRate (C : Finset Ω) (src : Source q G Ω) (s : Statement q G (k + 1)) (w : Ω) : ℚ :=
  match header src s w with
  | none => 0
  | some (msg, u) => ∏ i, rate C src (child_statement s msg (u i))

theorem rootRate_count (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (w : Ω) :
    rootRate C src s w = rootCount C src s w / ((tapes C k).card : ℚ) ^ 4 := by
  cases hh : header src s w with
  | none => simp [rootRate, rootCount, hh]
  | some p =>
    rcases p with ⟨msg, u⟩
    simp [rootRate, rootCount, hh, rate, Finset.prod_div_distrib, Nat.cast_prod]

/-- Exact finite law of total probability. No marginal independence is postulated. -/
theorem rate_node_exact (C : Finset Ω) (src : Source q G Ω) (s : Statement q G (k + 1)) :
    rate C src s = (∑ w ∈ C, rootRate C src s w) / C.card := by
  rw [rate, good_node_count]
  change (↑(∑ w ∈ C, rootCount C src s w) : ℚ) /
    ↑(C ×ˢ Fintype.piFinset (fun _ : Fin 4 => tapes C k)).card = _
  simp only [Finset.card_product, Fintype.card_piFinset_const, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sum, rootRate_count, ← Finset.sum_div]
  rw [div_div, mul_comm]

/-- Uniform lower bound over every accepted root seed, allowing context-dependent child rates. -/
theorem rate_node_lower (C : Finset Ω) (hC : C.Nonempty) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (B : Finset Ω) (hB : B ⊆ C) (b : ℚ) (hb : 0 ≤ b)
    (h : ∀ w ∈ B, ∃ msg u, header src s w = some (msg, u) ∧
      ∀ i, b ≤ rate C src (child_statement s msg (u i))) :
    (B.card / (C.card : ℚ)) * b ^ 4 ≤ rate C src s := by
  have hn (w) : 0 ≤ rootRate C src s w := by rw [rootRate_count]; positivity
  have hw (w) (hw : w ∈ B) : b ^ 4 ≤ rootRate C src s w := by
    obtain ⟨msg, u, he, hv⟩ := h w hw
    simp only [rootRate, he]
    calc b ^ 4 = ∏ _ : Fin 4, b := by simp
         _ ≤ _ := Finset.prod_le_prod (fun _ _ => hb) (fun i _ => hv i)
  have hl := (Finset.sum_le_sum hw).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hB (fun w _ _ => hn w))
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  rw [rate_node_exact]
  have hd := div_le_div_of_nonneg_right hl (le_of_lt hc)
  simpa [Finset.sum_const, nsmul_eq_mul, div_mul_eq_mul_div] using hd

theorem rate_node_positive (C : Finset Ω) (hC : C.Nonempty) (src : Source q G Ω)
    (s : Statement q G (k + 1)) (B : Finset Ω) (hB : B ⊆ C) (hne : B.Nonempty)
    (b : ℚ) (hb : 0 < b)
    (h : ∀ w ∈ B, ∃ msg u, header src s w = some (msg, u) ∧
      ∀ i, b ≤ rate C src (child_statement s msg (u i))) : 0 < rate C src s := by
  apply lt_of_lt_of_le _ (rate_node_lower C hC src s B hB b hb.le h)
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  have hbc : (0 : ℚ) < B.card := by exact_mod_cast hne.card_pos
  positivity

/-- A failed child for every valid root seed annihilates the entire experiment. -/
theorem rate_zero_of_blocked_child (C : Finset Ω) (src : Source q G Ω)
    (s : Statement q G (k + 1))
    (h : ∀ w ∈ C, ∀ msg u, header src s w = some (msg, u) →
      ∃ i, rate C src (child_statement s msg (u i)) = 0) : rate C src s = 0 := by
  rw [rate_node_exact]
  suffices ∀ w ∈ C, rootRate C src s w = 0 by simp [Finset.sum_eq_zero this]
  intro w hw
  cases hh : header src s w with
  | none => simp [rootRate, hh]
  | some p =>
    rcases p with ⟨msg, u⟩
    obtain ⟨i, hi⟩ := h w hw msg u hh
    simp only [rootRate, hh]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem positive_rate_extracts (C : Finset Ω) (src : Source q G Ω) (s : Statement q G k)
    (hp : 0 < rate C src s) :
    ∃ w ∈ tapes C k, ∃ r, extract src s w = .ok r ∧ ResultValid s r := by
  rw [rate_probability] at hp
  obtain ⟨w, hw, hg⟩ := positive_probability_has_outcome _ _ hp
  have hs := (Finset.mem_filter.mp hg).2
  cases he : generate src s w with
  | none => simp [he] at hs
  | some t => obtain ⟨r, hr⟩ := generated_extracts src s w t he; exact ⟨w, hw, r, hr⟩



/-- Local availability assumptions: leaves have density b; at least a fraction a
of root seeds have valid messages and recursively available computed contexts. -/
def Dense (C : Finset Ω) (src : Source q G Ω) (a b : ℚ) :
    {k : ℕ} → Statement q G k → Prop
  | 0, s => b ≤ rate C src s
  | _ + 1, s => ∃ B : Finset Ω, B ⊆ C ∧ a ≤ B.card / (C.card : ℚ) ∧
      ∀ w ∈ B, ∃ msg u, header src s w = some (msg, u) ∧
        ∀ i, Dense C src a b (child_statement s msg (u i))

def lowerBound (a b : ℚ) : ℕ → ℚ
  | 0 => b
  | k + 1 => a * lowerBound a b k ^ 4

theorem lowerBound_nonnegative (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    0 ≤ lowerBound a b k := by
  induction k with
  | zero => exact hb
  | succ k ih => exact mul_nonneg ha (pow_nonneg ih _)

theorem lowerBound_positive (a b : ℚ) (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    0 < lowerBound a b k := by
  induction k with
  | zero => exact hb
  | succ k ih => exact mul_pos ha (pow_pos ih _)

/-- Iterate the exact-context conditional bound through every level. -/
theorem recursive_probability_lower (C : Finset Ω) (hC : C.Nonempty)
    (src : Source q G Ω) (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (s : Statement q G k) (h : Dense C src a b s) :
    lowerBound a b k ≤ rate C src s := by
  induction k with
  | zero => exact h
  | succ k ih =>
    obtain ⟨B, hB, hd, hv⟩ := h
    have hr := rate_node_lower C hC src s B hB (lowerBound a b k)
      (lowerBound_nonnegative a b ha hb k) (by
        intro w hw
        obtain ⟨msg, u, he, hc⟩ := hv w hw
        exact ⟨msg, u, he, fun i => ih _ (hc i)⟩)
    exact (mul_le_mul_of_nonneg_right hd (by positivity)).trans hr

theorem dense_extracts (C : Finset Ω) (hC : C.Nonempty) (src : Source q G Ω)
    (a b : ℚ) (ha : 0 < a) (hb : 0 < b) (s : Statement q G k)
    (h : Dense C src a b s) :
    ∃ w ∈ tapes C k, ∃ r, extract src s w = .ok r ∧ ResultValid s r := by
  exact positive_rate_extracts C src s (lt_of_lt_of_le (lowerBound_positive a b ha hb k)
    (recursive_probability_lower C hC src a b ha.le hb.le s h))

/-- The concrete recursively generated event can also be retried on independent whole tapes. -/
theorem recursive_retry_bounds (C : Finset Ω) (hC : (tapes C k).Nonempty)
    (src : Source q G Ω) (s : Statement q G k) (T : ℕ) :
    CryptoBulletproofsIPABoundedRetryContract.RetryBounds
      (CryptoBulletproofsIPAProductTapeCandidateGeneratorContract.productTapes (tapes C k) T)
      (CryptoBulletproofsIPAProductTapeCandidateGeneratorContract.tapeAttempt
        (fun w => (generate src s w).isSome)) (fun _ => rate C src s) T := by
  exact CryptoBulletproofsIPAProductTapeCandidateGeneratorContract.product_retry_bounds
    (tapes C k) hC (fun w => (generate src s w).isSome) T

end Counting

/-- An independently checked complete output still has exactly 4^k scalar leaves. -/
def leafCount : {k : ℕ} → IPATranscriptTree q G k → ℕ
  | 0, .leaf _ _ _ => 1
  | _ + 1, .node _ _ _ ts => ∑ i, leafCount (ts i)

omit [Fact q.Prime] [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G] in
theorem leafCount_eq (t : IPATranscriptTree q G k) : leafCount t = 4 ^ k := by
  induction t with
  | leaf => rfl
  | node c msg u ts ih => simp [leafCount, ih, pow_succ, mul_comm]

structure CryptoBulletproofsIPARecursiveTreeGeneratorContractSuite : Prop where
  correctness : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (Ω : Type) (k : ℕ) (src : Source q G Ω) (s : Statement q G k)
    (w : Tape Ω k) (t : IPATranscriptTree q G k), generate src s w = some t →
      ValidAcceptingTree s t
  probability : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (Ω : Type) [DecidableEq Ω] (k : ℕ) (C : Finset Ω), C.Nonempty →
    ∀ (src : Source q G Ω) (a b : ℚ), 0 ≤ a → 0 ≤ b → ∀ (s : Statement q G k),
      Dense C src a b s → lowerBound a b k ≤ rate C src s
  extraction : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (Ω : Type) (k : ℕ) (src : Source q G Ω) (s : Statement q G k)
    (w : Tape Ω k) (r : TreeExtractionResult q k), extract src s w = .ok r → ResultValid s r

theorem verification_suite : CryptoBulletproofsIPARecursiveTreeGeneratorContractSuite where
  correctness := fun _ _ _ _ _ _ _ _ => generate_valid
  probability := fun _ _ _ _ _ _ _ _ _ => recursive_probability_lower
  extraction := fun _ _ _ _ _ _ _ _ => extract_sound

end CryptoBulletproofsIPARecursiveTreeGeneratorContract
