/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarForkProgressProbabilityContract
import Verification.CryptoBulletproofsIPAProductTapeCandidateGeneratorContract

/-! Independent finite full-probe schedules imply the actual collector's conditional
progress bounds. Success density is local to the fixed snapshot and includes child
acquisition. No global-acceptance, external-process, ROM or complexity claim. -/
namespace CryptoHiddenScalarForkScheduleProgressContract
open scoped BigOperators
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkProgressProbabilityContract
namespace Product
export CryptoBulletproofsIPAProductTapeCandidateGeneratorContract
  (productTapes product_card product_nonempty)
end Product

section Product
variable {U : Type} [DecidableEq U]

omit [DecidableEq U] in
/-- Resampling one coordinate preserves the finite product law. This identity is
valid for every function, including indicators of complete histories and outcomes. -/
theorem resample_sum (C : Finset U) (T : ℕ) (i : Fin T) (f : (Fin T → U) → ℚ) :
    (∑ w ∈ Product.productTapes C T, ∑ u ∈ C, f (Function.update w i u)) =
      C.card * ∑ w ∈ Product.productTapes C T, f w := by
  classical
  let D := Product.productTapes C T
  have hm (w : Fin T → U) (hw : w ∈ D) (u : U) (hu : u ∈ C) :
      Function.update w i u ∈ D := by
    simp only [D, Product.productTapes, Fintype.mem_piFinset] at *
    intro j
    by_cases h : j = i
    · subst j; simpa using hu
    · simpa [Function.update_of_ne h] using hw j
  have hi (w : Fin T → U) (hw : w ∈ D) : w i ∈ C :=
    (Fintype.mem_piFinset.mp hw) i
  have hs : (∑ p ∈ D ×ˢ C, f (Function.update p.1 i p.2)) =
      ∑ p ∈ D ×ˢ C, f p.1 := by
    refine Finset.sum_bij' (fun (p : (Fin T → U) × U) _ => (Function.update p.1 i p.2, p.1 i))
      (fun (p : (Fin T → U) × U) _ => (Function.update p.1 i p.2, p.1 i)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hw,hu⟩ := Finset.mem_product.mp hp
      exact Finset.mem_product.mpr ⟨hm _ hw _ hu, hi _ hw⟩
    · intro p hp
      obtain ⟨hw,hu⟩ := Finset.mem_product.mp hp
      exact Finset.mem_product.mpr ⟨hm _ hw _ hu, hi _ hw⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; rfl
  simpa only [Finset.sum_product, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum] using hs

/-- One fresh coordinate remains uniform even on an event unaffected by that
coordinate (in particular an event determined by its strict prefix). -/
theorem fresh_event_count (C : Finset U) (T : ℕ) (i : Fin T)
    (E : (Fin T → U) → Prop) [DecidablePred E]
    (hE : ∀ w u, E (Function.update w i u) ↔ E w) (B : Finset U) :
    ((Product.productTapes C T).filter (fun w => E w ∧ w i ∈ B)).card * C.card =
      ((Product.productTapes C T).filter E).card * (C ∩ B).card := by
  classical
  have hs := resample_sum C T i (fun w => if E w ∧ w i ∈ B then 1 else 0)
  simp only [Function.update_self, hE] at hs
  have he (w : Fin T → U) :
      (∑ u ∈ C, (if E w ∧ u ∈ B then (1 : ℚ) else 0)) =
        if E w then ((C ∩ B).card : ℚ) else 0 := by
    by_cases h : E w <;> simp [h, Finset.sum_ite_mem]
  simp_rw [he] at hs
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hnat : C.card * ((Product.productTapes C T).filter (fun w => E w ∧ w i ∈ B)).card =
      ((Product.productTapes C T).filter E).card * (C ∩ B).card := by exact_mod_cast hs.symm
  simpa [Nat.mul_comm] using hnat
omit [DecidableEq U] in
/-- Full-prefix resampling bounds aggregate to the count-conditioned bound used
by epsilon216. The premise is per concrete history, not a Markov assumption. -/
theorem resampling_progress (C : Finset U) (hC : C.Nonempty) (T : ℕ) (i : Fin T)
    (N : ℕ → (Fin T → U) → ℕ) (j : ℕ) (p : ℚ)
    (hprefix : ∀ w u, N i.val (Function.update w i u) = N i.val w)
    (hlocal : ∀ w ∈ Product.productTapes C T, N i.val w = j →
      p * C.card ≤ ((C.filter fun u => N (i.val + 1) (Function.update w i u) = j + 1).card : ℚ)) :
    p * ((Product.productTapes C T).filter (fun w => N i.val w = j)).card ≤
      (((Product.productTapes C T).filter
        (fun w => N i.val w = j ∧ N (i.val + 1) w = j + 1)).card : ℚ) := by
  classical
  let D := Product.productTapes C T
  have h (w : Fin T → U) (hw : w ∈ D) :
      p * C.card * (if N i.val w = j then 1 else 0) ≤
        ∑ u ∈ C, (if N i.val (Function.update w i u) = j ∧
          N (i.val + 1) (Function.update w i u) = j + 1 then (1 : ℚ) else 0) := by
    simp only [hprefix]
    by_cases he : N i.val w = j
    · simpa [he, ← Finset.sum_filter] using hlocal w hw he
    · simp [he]
  have hs := Finset.sum_le_sum h
  rw [resample_sum C T i (fun w => if N i.val w = j ∧ N (i.val + 1) w = j + 1 then 1 else 0)] at hs
  rw [← Finset.mul_sum] at hs
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  dsimp [D] at hs
  nlinarith

end Product

section Collector
variable {U I V K : Type} [DecidableEq U] [DecidableEq K]

def iidSchedule (draw : U → I) {T : ℕ} (w : Fin T → U) : List I :=
  List.ofFn (fun i => draw (w i))

omit [DecidableEq U] in
@[simp] theorem iidSchedule_length (draw : U → I) {T : ℕ} (w : Fin T → U) :
    (iidSchedule draw w).length = T := by simp [iidSchedule]

omit [DecidableEq U] in
/-- The actual collector prefix does not inspect the next or later probe. -/
theorem schedule_prefix_update (draw : U → I) {T : ℕ} (w : Fin T → U)
    (i : Fin T) (u : U) :
    (iidSchedule draw (Function.update w i u)).take i.val =
      (iidSchedule draw w).take i.val := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have hj : j < i.val := by simpa using (lt_of_lt_of_le h₁ (List.length_take_le _ _))
    have hne : (⟨j, lt_trans hj i.isLt⟩ : Fin T) ≠ i := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp [iidSchedule, Function.update_of_ne hne]

def successSeeds (C : Finset U) (draw : U → I) (attempt : I → Attempt V) : Finset U :=
  C.filter fun u => (attempt (draw u)).value.isSome

def classSeeds (C : Finset U) (draw : U → I) (label : I → K) (k : K) : Finset U :=
  C.filter fun u => label (draw u) = k

def blockedSeeds (C : Finset U) (draw : U → I) (label : I → K) (S : Finset K) : Finset U :=
  C.filter fun u => label (draw u) ∈ S

/-- Union bound on occupied classes under the actual law of full microseeds. -/
theorem blocked_mass_le (C : Finset U) (hC : C.Nonempty) (draw : U → I)
    (label : I → K) (S : Finset K) (beta : ℚ)
    (hb : ∀ k, Prob.probability C (classSeeds C draw label k) ≤ beta) :
    Prob.probability C (blockedSeeds C draw label S) ≤ S.card * beta := by
  have hpos : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  have he : (blockedSeeds C draw label S).card =
      ∑ k ∈ S, (classSeeds C draw label k).card :=
    (Finset.sum_card_fiberwise_eq_card_filter C S (fun u => label (draw u))).symm
  have hk (k : K) : ((classSeeds C draw label k).card : ℚ) ≤ beta * C.card := by
    have h := hb k
    have hs : classSeeds C draw label k ⊆ C := Finset.filter_subset _ _
    rw [Prob.probability, Finset.inter_eq_left.mpr hs] at h
    exact (div_le_iff₀ hpos).mp h
  unfold Prob.probability
  rw [Finset.inter_eq_left.mpr (show blockedSeeds C draw label S ⊆ C from
    Finset.filter_subset _ _)]
  apply (div_le_iff₀ hpos).mpr
  rw [he, Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ S, beta * (C.card : ℚ) := Finset.sum_le_sum (fun k _ => hk k)
    _ = _ := by simp; ring

/-- One actual scan step adds a value exactly on successful unblocked probes. -/
theorem scan_step_progress (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (acc : List V) (ha : acc.length < n) (x : I) :
    (scan n label key attempt [x] acc).1.length = acc.length + 1 ↔
      (attempt x).value.isSome = true ∧ label x ∉ acc.map key := by
  have hn : acc.length ≠ n := by omega
  by_cases hd : label x ∈ acc.map key
  · simp [scan, hn, hd]
  · cases hv : (attempt x).value <;> simp [scan, hn, hd, hv]
    split_ifs <;> simp

/-- Concrete iid sampler adapter. d concerns full child acquisition; beta bounds
one class under the same microseed law. Success and class need not be independent. -/
theorem iid_progress_bounds
    (n : ℕ) (C : Finset U) (hC : C.Nonempty)
    (draw : U → I) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (hc : KeyCoherent label key attempt)
    (d beta : ℚ) (_hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hb : 0 ≤ beta)
    (hgood : d ≤ Prob.probability C (successSeeds C draw attempt))
    (hclass : ∀ k, Prob.probability C (classSeeds C draw label k) ≤ beta)
    (T : ℕ) :
    ProgressBounds (Product.productTapes C T)
      (scanCounts n label key attempt (iidSchedule draw)) n T
      (fun j => max 0 (d - (j : ℚ) * beta)) := by
  classical
  constructor
  · intro j _
    exact ⟨le_max_left _ _, max_le (by norm_num)
      (le_trans (sub_le_self d (mul_nonneg (Nat.cast_nonneg _) hb)) hd1)⟩
  intro i hi j hj
  let ix : Fin T := ⟨i,hi⟩
  let N := scanCounts n label key attempt (@iidSchedule U I draw T)
  have hpref (w : Fin T → U) (u : U) : N i (Function.update w ix u) = N i w := by
    simp only [N, scanCounts, retainedCount]
    rw [schedule_prefix_update draw w ix u]
  apply resampling_progress C hC T ix N j _ hpref
  intro w _hw hw
  let acc := (scan n label key attempt ((iidSchedule draw w).take i) []).1
  have hlen : acc.length = j := hw
  have hinv := scan_invariants n label key attempt hc ((iidSchedule draw w).take i) []
    (Nat.zero_le _) (by simp)
  let S := (acc.map key).toFinset
  have hcard : S.card = j := by
    rw [List.toFinset_card_of_nodup hinv.2, List.length_map, hlen]
  have hmass := blocked_mass_le C hC draw label S beta hclass
  rw [hcard] at hmass
  have hlo := unblocked_probability_lower C (successSeeds C draw attempt)
    (blockedSeeds C draw label S) hC (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) d ((j : ℚ) * beta) hgood hmass
  have hstep (u : U) :
      N (i + 1) (Function.update w ix u) = j + 1 ↔
        (attempt (draw u)).value.isSome = true ∧ label (draw u) ∉ acc.map key := by
    unfold N scanCounts retainedCount
    rw [List.take_succ_eq_append_getElem (by simpa using hi), scan_append,
      schedule_prefix_update draw w ix u]
    simp only [iidSchedule, List.getElem_ofFn]
    simp only [ix, Function.update_self]
    change (scan n label key attempt [draw u] acc).1.length = j + 1 ↔ _
    rw [← hlen]
    exact scan_step_progress n label key attempt acc (by omega) (draw u)
  have he : C.filter (fun u => N (i + 1) (Function.update w ix u) = j + 1) =
      successSeeds C draw attempt \ blockedSeeds C draw label S := by
    ext u
    simp only [Finset.mem_filter, hstep, Finset.mem_sdiff, successSeeds, blockedSeeds,
      S, List.mem_toFinset]
    tauto
  have hcpos : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  have hsub : successSeeds C draw attempt \ blockedSeeds C draw label S ⊆ C :=
    Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _)
  rw [Prob.probability, Finset.inter_eq_left.mpr hsub] at hlo
  rw [he]
  exact (le_div_iff₀ hcpos).mp hlo

/-- Success probability for the unchanged collector with finite iid full probes. -/
theorem iid_collect_probability_lower
    (n : ℕ) (C : Finset U) (hC : C.Nonempty)
    (draw : U → I) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (hc : KeyCoherent label key attempt)
    (d beta : ℚ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hb : 0 ≤ beta)
    (hgood : d ≤ Prob.probability C (successSeeds C draw attempt))
    (hclass : ∀ k, Prob.probability C (classSeeds C draw label k) ≤ beta)
    (T : ℕ) :
    quotaLower n (fun j => max 0 (d - (j : ℚ) * beta)) T 0 ≤
      Prob.probability (Product.productTapes C T)
        ((Product.productTapes C T).filter fun w =>
          (collect n label key attempt (iidSchedule draw w)).value.isSome) :=
  collect_probability_lower n label key attempt hc _ (Product.product_nonempty C hC T)
    (iidSchedule draw) T (fun w _ => iidSchedule_length draw w) _
    (iid_progress_bounds n C hC draw label key attempt hc d beta hd0 hd1 hb hgood hclass T)

/-- A counted fiber bound is a probability bound for uniform microseeds. It
applies to nonuniform candidate laws represented by multiple microseeds too. -/
theorem class_mass_of_card_le (C : Finset U) (_hC : C.Nonempty) (draw : U → I)
    (label : I → K) (m : ℕ)
    (hf : ∀ k, (classSeeds C draw label k).card ≤ m) :
    ∀ k, Prob.probability C (classSeeds C draw label k) ≤ (m : ℚ) / C.card := by
  intro k
  rw [Prob.probability, Finset.inter_eq_left.mpr
    (show classSeeds C draw label k ⊆ C from Finset.filter_subset _ _)]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hf k) (by positivity)

end Collector
section Acquisition
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
  [DecidableEq A] {Ω S U : Type} [DecidableEq U] {k : ℕ}

theorem iid_tree_probability_lower (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (hs : ReachableSnapshot m s) (st : Statement q A (k + 1)) (lr : RoundMessages A)
    (seeds : Finset U) (hne : seeds.Nonempty) (draw : U → (ZMod q)ˣ × IPASchedule q k)
    (d beta : ℚ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hb : 0 ≤ beta)
    (hgood : d ≤ Prob.probability seeds (successSeeds seeds draw (roundAttempt m s hs st lr)))
    (hclass : ∀ x, Prob.probability seeds
      (classSeeds seeds draw (fun pr => (pr.1 : ZMod q) ^ 2) x) ≤ beta) (T : ℕ) :
    quotaLower 4 (fun j => max 0 (d - (j : ℚ) * beta)) T 0 ≤
      Prob.probability (Product.productTapes seeds T)
        ((Product.productTapes seeds T).filter fun w =>
          (acquireTree m s hs (.round lr) st (iidSchedule draw w)).value.isSome) := by
  simp_rw [tree_collect_event]
  exact iid_collect_probability_lower 4 seeds hne draw _ _ _
    (round_key_coherent m s hs st lr) d beta hd0 hd1 hb hgood hclass T

theorem iid_node_probability_lower (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A) (e t z : ZMod q)
    (o : Observation m s (.outer e)) (ho : query m s (.outer e) = some o)
    (ha : o.packet = .scalar t z) (hv : C.scalarCheck p ann e t z)
    (seeds : Finset U) (hne : seeds.Nonempty) (draw : U → (ZMod q)ˣ × IPASchedule q k)
    (d beta : ℚ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hb : 0 ≤ beta)
    (hgood : d ≤ Prob.probability seeds
      (successSeeds seeds draw (etaAttempt p m o.after (o.reachable hs) ann e t)))
    (hclass : ∀ x, Prob.probability seeds (classSeeds seeds draw Prod.fst x) ≤ beta)
    (T : ℕ) :
    quotaLower 2 (fun j => max 0 (d - (j : ℚ) * beta)) T 0 ≤
      Prob.probability (Product.productTapes seeds T)
        ((Product.productTapes seeds T).filter fun w =>
          (acquireNode p m s hs ann e (iidSchedule draw w)).value.isSome) := by
  simp_rw [node_collect_event p m s hs ann e t z o ho ha hv]
  exact iid_collect_probability_lower 2 seeds hne draw _ _ _
    (eta_key_coherent p m o.after (o.reachable hs) ann e t)
    d beta hd0 hd1 hb hgood hclass T

theorem iid_acquisition_probability_lower (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (o : Observation m (initialSnapshot m) .commit) (ann : F.Announcement A)
    (ho : query m (initialSnapshot m) .commit = some o) (ha : o.packet = .announcement ann)
    (seeds : Finset U) (hne : seeds.Nonempty) (draw : U → ZMod q × EtaSchedule q k)
    (d beta : ℚ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hb : 0 ≤ beta)
    (hgood : d ≤ Prob.probability seeds (successSeeds seeds draw
      (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2)))
    (hclass : ∀ x, Prob.probability seeds (classSeeds seeds draw Prod.fst x) ≤ beta)
    (T : ℕ) :
    quotaLower 3 (fun j => max 0 (d - (j : ℚ) * beta)) T 0 ≤
      Prob.probability (Product.productTapes seeds T)
        ((Product.productTapes seeds T).filter fun w =>
          (acquireCompressedFork p m (iidSchedule draw w)).outcome.isOk) := by
  simp_rw [acquisition_collect_event p m o ann ho ha]
  exact iid_collect_probability_lower 3 seeds hne draw _ _ _
    (outer_key_coherent p m o.after (o.reachable .initial) ann)
    d beta hd0 hd1 hb hgood hclass T

/-- Positive concrete iid bound yields an actual sampled schedule, model
provenance and the existing witness-or-relation extraction conclusion. -/
theorem iid_positive_extracts (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (o : Observation m (initialSnapshot m) .commit) (ann : F.Announcement A)
    (ho : query m (initialSnapshot m) .commit = some o) (ha : o.packet = .announcement ann)
    (seeds : Finset U) (hne : seeds.Nonempty) (draw : U → ZMod q × EtaSchedule q k)
    (d beta : ℚ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hb : 0 ≤ beta)
    (hgood : d ≤ Prob.probability seeds (successSeeds seeds draw
      (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2)))
    (hclass : ∀ x, Prob.probability seeds (classSeeds seeds draw Prod.fst x) ≤ beta)
    (T : ℕ) (hpos : 0 < quotaLower 3 (fun j => max 0 (d - (j : ℚ) * beta)) T 0) :
    ∃ w ∈ Product.productTapes seeds T, ∃ f,
      (acquireCompressedFork p m (iidSchedule draw w)).outcome = .ok f ∧
      ForkProvenance m f ∧ F.ResultValid p (C.extractCompressed p f) :=
  positive_schedule_probability_extracts p m _ (iidSchedule draw)
    (hpos.trans_le (iid_acquisition_probability_lower p m o ann ho ha seeds hne draw
      d beta hd0 hd1 hb hgood hclass T))
end Acquisition

structure CryptoHiddenScalarForkScheduleProgressContractSuite : Prop where
  iid_bound : ∀ (U I V K : Type) [DecidableEq U] [DecidableEq K]
    (n : ℕ) (C : Finset U), C.Nonempty →
    ∀ (draw : U → I) (label : I → K) (key : V → K) (attempt : I → Attempt V),
    KeyCoherent label key attempt → ∀ d beta : ℚ, 0 ≤ d → d ≤ 1 → 0 ≤ beta →
    d ≤ Prob.probability C (successSeeds C draw attempt) →
    (∀ k, Prob.probability C (classSeeds C draw label k) ≤ beta) → ∀ T,
    ProgressBounds (Product.productTapes C T)
      (scanCounts n label key attempt (iidSchedule draw)) n T (fun j => max 0 (d - (j : ℚ) * beta))
  collector_bound : ∀ (U I V K : Type) [DecidableEq U] [DecidableEq K]
    (n : ℕ) (C : Finset U), C.Nonempty →
    ∀ (draw : U → I) (label : I → K) (key : V → K) (attempt : I → Attempt V),
    KeyCoherent label key attempt → ∀ d beta : ℚ, 0 ≤ d → d ≤ 1 → 0 ≤ beta →
    d ≤ Prob.probability C (successSeeds C draw attempt) →
    (∀ k, Prob.probability C (classSeeds C draw label k) ≤ beta) → ∀ T,
    quotaLower n (fun j => max 0 (d - (j : ℚ) * beta)) T 0 ≤
      Prob.probability (Product.productTapes C T) ((Product.productTapes C T).filter fun w =>
        (collect n label key attempt (iidSchedule draw w)).value.isSome)

theorem verification_suite : CryptoHiddenScalarForkScheduleProgressContractSuite where
  iid_bound := fun _ _ _ _ _ _ => iid_progress_bounds
  collector_bound := fun _ _ _ _ _ _ => iid_collect_probability_lower
end CryptoHiddenScalarForkScheduleProgressContract
