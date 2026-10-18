/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAFiniteForkingProbabilityContract
import Verification.CryptoBulletproofsTreeExtraction

/-! Finite correlated random tapes, sequential conditional bounds, and complete
context-valid four-branch IPA trees. No adaptive oracle or complexity claim. -/
namespace CryptoBulletproofsIPATreeProbabilityContract
open scoped BigOperators

section FiniteExperiment
variable {Ω : Type} [DecidableEq Ω]

/-- Uniform mass of an event inside the supplied finite tape space. -/
def probability (C E : Finset Ω) : ℚ := (E ∩ C).card / (C.card : ℚ)

/-- All ordered local tests must pass on the SAME tape. -/
def passing (C : Finset Ω) (tests : List (Ω → Bool)) : Finset Ω :=
  C.filter (fun w => tests.all (fun f => f w))

omit [DecidableEq Ω] in
@[simp] theorem passing_nil (C : Finset Ω) : passing C [] = C := by simp [passing]

omit [DecidableEq Ω] in
@[simp] theorem passing_cons (C : Finset Ω) (f : Ω → Bool) (fs : List (Ω → Bool)) :
    passing C (f :: fs) = passing (C.filter (fun w => f w)) fs := by
  ext w
  simp [passing, and_assoc]

omit [DecidableEq Ω] in
theorem passing_subset (C : Finset Ω) (fs : List (Ω → Bool)) : passing C fs ⊆ C :=
  Finset.filter_subset _ _

/-- A bound for each test, conditioned on ALL previous successes. Multiplicative
cardinality form is meaningful even after a zero-probability prefix. -/
def ConditionalBounds : Finset Ω → List (Ω → Bool) → List ℚ → Prop
  | _, [], [] => True
  | C, f :: fs, b :: bs => 0 ≤ b ∧ b ≤ 1 ∧
      b * C.card ≤ ((C.filter (fun w => f w)).card : ℚ) ∧
      ConditionalBounds (C.filter (fun w => f w)) fs bs
  | _, _, _ => False

instance conditionalBoundsDecidable (C : Finset Ω) (fs : List (Ω → Bool)) (bs : List ℚ) :
    Decidable (ConditionalBounds C fs bs) := by
  induction fs generalizing C bs with
  | nil => cases bs <;> unfold ConditionalBounds <;> infer_instance
  | cons f fs ih =>
    cases bs with
    | nil => unfold ConditionalBounds; infer_instance
    | cons b bs =>
      unfold ConditionalBounds
      have := ih (C.filter (fun w => f w)) bs
      infer_instance

theorem conditional_step_iff (C : Finset Ω) (f : Ω → Bool) (b : ℚ)
    (hC : C.Nonempty) :
    b * C.card ≤ ((C.filter (fun w => f w)).card : ℚ) ↔
      b ≤ probability C (C.filter (fun w => f w)) := by
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  simp only [probability, Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
  exact (le_div_iff₀ hc).symm

omit [DecidableEq Ω] in
theorem conditional_bounds_length (C : Finset Ω) (fs : List (Ω → Bool)) (bs : List ℚ)
    (h : ConditionalBounds C fs bs) : fs.length = bs.length := by
  induction fs generalizing C bs with
  | nil => cases bs <;> simp_all [ConditionalBounds]
  | cons f fs ih =>
    cases bs with
    | nil => simp [ConditionalBounds] at h
    | cons b bs => simpa using ih _ _ h.2.2.2

omit [DecidableEq Ω] in
theorem conditional_product_nonnegative (C : Finset Ω) (fs : List (Ω → Bool)) (bs : List ℚ)
    (h : ConditionalBounds C fs bs) : 0 ≤ bs.prod := by
  induction fs generalizing C bs with
  | nil => cases bs <;> simp_all [ConditionalBounds]
  | cons f fs ih =>
    cases bs with
    | nil => simp [ConditionalBounds] at h
    | cons b bs => simpa only [List.prod_cons] using mul_nonneg h.1 (ih _ _ h.2.2.2)

omit [DecidableEq Ω] in
theorem sequential_count_lower (C : Finset Ω) (fs : List (Ω → Bool)) (bs : List ℚ)
    (h : ConditionalBounds C fs bs) : bs.prod * C.card ≤ ((passing C fs).card : ℚ) := by
  induction fs generalizing C bs with
  | nil => cases bs <;> simp_all [ConditionalBounds]
  | cons f fs ih =>
    cases bs with
    | nil => simp [ConditionalBounds] at h
    | cons b bs =>
      have tail := ih _ _ h.2.2.2
      have hn := conditional_product_nonnegative _ _ _ h.2.2.2
      have step := mul_le_mul_of_nonneg_left h.2.2.1 hn
      rw [passing_cons, List.prod_cons]
      nlinarith

theorem sequential_probability_lower (C : Finset Ω) (hC : C.Nonempty)
    (fs : List (Ω → Bool)) (bs : List ℚ) (h : ConditionalBounds C fs bs) :
    bs.prod ≤ probability C (passing C fs) := by
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  rw [probability, Finset.inter_eq_left.mpr (passing_subset C fs)]
  exact (le_div_iff₀ hc).mpr (sequential_count_lower C fs bs h)

theorem positive_probability_has_outcome (C E : Finset Ω) (h : 0 < probability C E) :
    ∃ w ∈ C, w ∈ E := by
  have hn : (E ∩ C).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [probability, hz] at h
  obtain ⟨w, hw⟩ := hn
  exact ⟨w, (Finset.mem_inter.mp hw).2, (Finset.mem_inter.mp hw).1⟩
theorem probability_nonnegative (C E : Finset Ω) : 0 ≤ probability C E := by
  unfold probability
  positivity

theorem probability_le_one (C E : Finset Ω) (hC : C.Nonempty) : probability C E ≤ 1 := by
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  apply (div_le_one hc).mpr
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : E ∩ C ⊆ C)

theorem probability_mono (C E D : Finset Ω) (h : E ⊆ D) :
    probability C E ≤ probability C D := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right h)

end FiniteExperiment

open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction

/-- One check per internal node and scalar leaf: 1,5,21,... -/
def checkCount : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + 4 * checkCount k

theorem checkCount_positive (k : ℕ) : 0 < checkCount k := by cases k <;> simp [checkCount]

section Tree
variable {q : ℕ} [Fact q.Prime] {G : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] {k : ℕ}

/-- Preorder validation. Children use independently computed contexts, never
merely their claimed statements. Invalid nonzero guards produce a rejecting tape
of the same fixed length. -/
def localChecks : {k : ℕ} → Statement q G k → IPATranscriptTree q G k → List Bool
  | 0, s, .leaf c a b => [decide (c = s ∧ s.P = a • s.G 0 + b • s.H 0 + (a * b) • s.U)]
  | k + 1, s, .node c msg u ts =>
    if hn : ∀ i, u i ≠ 0 then
      [decide (c = s ∧ Function.Injective (fun i => u i ^ 2))] ++
      localChecks (child_statement s msg (Units.mk0 (u 0) (hn 0))) (ts 0) ++
      localChecks (child_statement s msg (Units.mk0 (u 1) (hn 1))) (ts 1) ++
      localChecks (child_statement s msg (Units.mk0 (u 2) (hn 2))) (ts 2) ++
      localChecks (child_statement s msg (Units.mk0 (u 3) (hn 3))) (ts 3)
    else List.replicate (checkCount (k + 1)) false

theorem localChecks_length (s : Statement q G k) (t : IPATranscriptTree q G k) :
    (localChecks s t).length = checkCount k := by
  induction t with
  | leaf c a b => rfl
  | node c msg u ts ih =>
    simp only [localChecks]
    split_ifs
    · simp only [List.length_append, List.length_singleton, ih, checkCount]
      omega
    · simp

theorem localChecks_valid (s : Statement q G k) (t : IPATranscriptTree q G k) :
    (localChecks s t).all id = true ↔ ValidAcceptingTree s t := by
  induction t with
  | leaf c a b => simp [localChecks, ValidAcceptingTree]
  | node c msg u ts ih =>
    simp only [localChecks, ValidAcceptingTree]
    split_ifs with hn
    · simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
        id_eq, Bool.and_eq_true, decide_eq_true_eq, ih]
      simp [Fin.forall_fin_succ, and_assoc]
    · simp [checkCount]

variable {Ω : Type} [DecidableEq Ω]

/-- A single finite tape may correlate every branch and every level. -/
def treeTests (s : Statement q G k) (generate : Ω → IPATranscriptTree q G k) :
    List (Ω → Bool) :=
  List.ofFn (fun i : Fin (checkCount k) => fun w =>
    (localChecks s (generate w))[i.val]'(by rw [localChecks_length]; exact i.isLt))

omit [DecidableEq Ω] in
theorem treeTests_pass_iff (s : Statement q G k) (generate : Ω → IPATranscriptTree q G k)
    (w : Ω) : (treeTests s generate).all (fun f => f w) = true ↔
      ValidAcceptingTree s (generate w) := by
  rw [← localChecks_valid]
  simp only [treeTests, List.all_eq_true, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff]
  constructor
  · intro h b hb
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hb
    have v := h ⟨i, by simpa [localChecks_length] using hi⟩
    simpa [he] using v
  · intro h i
    exact h _ (List.getElem_mem _)

def validOutcomes (C : Finset Ω) (s : Statement q G k)
    (generate : Ω → IPATranscriptTree q G k) : Finset Ω :=
  C.filter (fun w => ValidAcceptingTree s (generate w))

omit [DecidableEq Ω] in
theorem passing_treeTests (C : Finset Ω) (s : Statement q G k)
    (generate : Ω → IPATranscriptTree q G k) :
    passing C (treeTests s generate) = validOutcomes C s generate := by
  ext w
  simp only [passing, validOutcomes, Finset.mem_filter, treeTests_pass_iff]

theorem tree_probability_lower (C : Finset Ω) (hC : C.Nonempty) (s : Statement q G k)
    (generate : Ω → IPATranscriptTree q G k) (bs : List ℚ)
    (h : ConditionalBounds C (treeTests s generate) bs) :
    bs.prod ≤ probability C (validOutcomes C s generate) := by
  rw [← passing_treeTests]
  exact sequential_probability_lower C hC _ bs h

theorem tree_uniform_lower (C : Finset Ω) (hC : C.Nonempty) (s : Statement q G k)
    (generate : Ω → IPATranscriptTree q G k) (p : ℚ)
    (h : ConditionalBounds C (treeTests s generate) (List.replicate (checkCount k) p)) :
    p ^ checkCount k ≤ probability C (validOutcomes C s generate) := by
  simpa using tree_probability_lower C hC s generate _ h

omit [DecidableEq Ω] in
theorem generated_tree_extracts (C : Finset Ω) (s : Statement q G k)
    (generate : Ω → IPATranscriptTree q G k) (w : Ω) (hw : w ∈ validOutcomes C s generate) :
    ∃ r, checked_extract s (generate w) = .ok r ∧ ResultValid s r := by
  have hv := (Finset.mem_filter.mp hw).2
  exact ⟨extractTree (generate w), by simp [checked_extract, hv],
    tree_extraction_soundness s (generate w) hv⟩

theorem positive_tree_probability_extracts (C : Finset Ω) (s : Statement q G k)
    (generate : Ω → IPATranscriptTree q G k)
    (hp : 0 < probability C (validOutcomes C s generate)) :
    ∃ w ∈ C, ∃ r, checked_extract s (generate w) = .ok r ∧ ResultValid s r := by
  obtain ⟨w, hw, hv⟩ := positive_probability_has_outcome C _ hp
  obtain ⟨r, hr⟩ := generated_tree_extracts C s generate w hv
  exact ⟨w, hw, r, hr⟩

omit [DecidableEq Ω] in
theorem conditional_tree_dichotomy (C : Finset Ω) (hC : C.Nonempty) (s : Statement q G k)
    (generate : Ω → IPATranscriptTree q G k) (bs : List ℚ)
    (h : ConditionalBounds C (treeTests s generate) bs) (hp : 0 < bs.prod) :
    (∃ a b : Vec k (ZMod q), s.P = ipa_target s.U s.G s.H a b) ∨
    (∃ c, c ≠ 0 ∧ evaluate s c = 0) := by
  classical
  have ht := tree_probability_lower C hC s generate bs h
  obtain ⟨_, _, r, _, hv⟩ := positive_tree_probability_extracts C s generate (lt_of_lt_of_le hp ht)
  cases r with
  | witness a b => exact Or.inl ⟨a, b, hv⟩
  | relation c => exact Or.inr ⟨c, hv⟩
omit [DecidableEq Ω] in
theorem extractor_event_eq (C : Finset Ω) (s : Statement q G k)
    (generate : Ω → IPATranscriptTree q G k) :
    C.filter (fun w => (checked_extract s (generate w)).isOk = true) =
      validOutcomes C s generate := by
  ext w
  simp [validOutcomes, checked_extract_success_iff]

end Tree

section FourDrawBridge
open CryptoBulletproofsIPAForkingExtractionContract
open CryptoBulletproofsIPAFiniteForkingProbabilityContract
variable {q : ℕ} [Fact q.Prime] {G : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] {k : ℕ}

/-- Actual four-draw output, with completed child responses supplied by the
experiment. Malformed lengths use a rejecting fallback. -/
def drawTree (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (replies : ZMod q → Option (IPATranscriptTree q G k)) :
    List (ZMod q) → IPATranscriptTree q G (k + 1)
  | [a,b,c,d] => .node s msg ![a,b,c,d]
      (fun i => (replies (![a,b,c,d] i)).getD (emptyTree k))
  | _ => emptyTree (k + 1)

omit [DecidableEq G] in
theorem accepted_draws_valid (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q G k))
    (hv : ∀ x (hx : x ≠ 0) t, replies x = some t →
      ValidAcceptingTree (child_statement s msg (Units.mk0 x hx)) t)
    (l : List (ZMod q)) (hl : l ∈ successes (replySet calls replies) 4) :
    ValidAcceptingTree s (drawTree s msg replies l) := by
  classical
  obtain ⟨a,b,c,d,rfl⟩ := List.length_eq_four.mp ((mem_successes _ _ _).mp hl).1
  obtain ⟨r, hr, _⟩ := sampled_fork_extracts s msg calls replies ![a,b,c,d]
    (sampled_success_isFork _ a b c d hl) hv
  have hh : (checked_extract s (drawTree s msg replies [a,b,c,d])).isOk = true := by
    simpa only [drawTree, hr] using (show (Except.ok r : Except String _).isOk = true from rfl)
  exact (checked_extract_success_iff _ _).mp hh

/-- With context-valid children, the epsilon204 root bound is also a lower bound
for the generated complete tree. For k=0 these children are scalar leaves. -/
theorem four_draw_tree_probability_lower (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q G k))
    (hv : ∀ x (hx : x ≠ 0) t, replies x = some t →
      ValidAcceptingTree (child_statement s msg (Units.mk0 x hx)) t) :
    successProbability calls.toFinset (replySet calls replies) ≤
      probability (samples calls.toFinset 4)
        (validOutcomes (samples calls.toFinset 4) s (drawTree s msg replies)) := by
  have hs := successes_subset_samples (replySet_subset_calls calls replies) 4
  have incl : successes (replySet calls replies) 4 ⊆
      validOutcomes (samples calls.toFinset 4) s (drawTree s msg replies) := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨hs hl, accepted_draws_valid s msg calls replies hv l hl⟩
  have h := probability_mono (samples calls.toFinset 4) _ _ incl
  simpa only [probability, Finset.inter_eq_left.mpr hs, card_samples,
    Nat.cast_pow, successProbability] using h

end FourDrawBridge
structure CryptoBulletproofsIPATreeProbabilityContractSuite : Prop where
  sequential : ∀ (Ω : Type) [DecidableEq Ω] (C : Finset Ω), C.Nonempty →
    ∀ (fs : List (Ω → Bool)) (bs : List ℚ), ConditionalBounds C fs bs →
      bs.prod ≤ probability C (passing C fs)
  validation : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (k : ℕ) (s : Statement q G k) (t : IPATranscriptTree q G k),
    (localChecks s t).all id = true ↔ ValidAcceptingTree s t
  whole_tree : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (Ω : Type) [DecidableEq Ω] (k : ℕ) (C : Finset Ω), C.Nonempty →
    ∀ (s : Statement q G k) (generate : Ω → IPATranscriptTree q G k) (bs : List ℚ),
      ConditionalBounds C (treeTests s generate) bs →
      bs.prod ≤ probability C (validOutcomes C s generate)
  extraction : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (Ω : Type) [DecidableEq Ω] (k : ℕ) (C : Finset Ω) (s : Statement q G k)
    (generate : Ω → IPATranscriptTree q G k),
    0 < probability C (validOutcomes C s generate) →
    ∃ w ∈ C, ∃ r, checked_extract s (generate w) = .ok r ∧ ResultValid s r

theorem verification_suite : CryptoBulletproofsIPATreeProbabilityContractSuite where
  sequential := fun _ _ => sequential_probability_lower
  validation := fun _ _ _ _ _ _ _ => localChecks_valid
  whole_tree := fun _ _ _ _ _ _ _ _ _ => tree_probability_lower
  extraction := fun _ _ _ _ _ _ _ _ _ => positive_tree_probability_extracts

end CryptoBulletproofsIPATreeProbabilityContract
