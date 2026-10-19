/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarForkScheduleProgressContract

/-! Child-law averaging discharges the full-probe density premise of epsilon217.
All rates refer to the actual reachable snapshot and the stated finite product law.
No global-acceptance, external-process, ROM or polynomial-time inference. -/
namespace CryptoHiddenScalarForkLocalDensityContract
open scoped BigOperators
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkScheduleProgressContract

section Finite
variable {U W I V K : Type} [DecidableEq U] [DecidableEq W] [DecidableEq K]

def average (C : Finset U) (f : U → ℚ) : ℚ := (∑ u ∈ C, f u) / C.card

/-- Exact total probability under uniform product microseeds; draw may be many-to-one. -/
theorem product_event_average (C : Finset U) (D : Finset W)
    (E : U → W → Bool) :
    Prob.probability (C ×ˢ D) ((C ×ˢ D).filter fun uv => E uv.1 uv.2) =
      average C (fun u => Prob.probability D (D.filter fun v => E u v)) := by
  simp only [Prob.probability, Finset.inter_eq_left.mpr (Finset.filter_subset _ _),
    Finset.card_filter, Finset.sum_product, Finset.card_product, Nat.cast_mul,
    Nat.cast_sum, average, ← Finset.sum_div]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [div_div, mul_comm]

/-- Exact full-probe rate; the entire child schedule is part of draw. -/
theorem full_probe_rate_eq_average (C : Finset U) (D : Finset W)
    (draw : U → W → I) (attempt : I → Attempt V) :
    Prob.probability (C ×ˢ D)
      (successSeeds (C ×ˢ D) (fun uv => draw uv.1 uv.2) attempt) =
      average C (fun u => Prob.probability D (successSeeds D (draw u) attempt)) :=
  product_event_average C D (fun u v => (attempt (draw u v)).value.isSome)

omit [DecidableEq U] in
theorem average_mono (C : Finset U) (f g : U → ℚ) (h : ∀ u ∈ C, f u ≤ g u) :
    average C f ≤ average C g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

omit [DecidableEq U] in
theorem average_bounds (C : Finset U) (hC : C.Nonempty) (f : U → ℚ)
    (h : ∀ u ∈ C, 0 ≤ f u ∧ f u ≤ 1) : 0 ≤ average C f ∧ average C f ≤ 1 := by
  have hc : (0 : ℚ) < C.card := by exact_mod_cast hC.card_pos
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun u hu => (h u hu).1) hc.le
  · have hs := Finset.sum_le_sum (fun u hu => (h u hu).2)
    simpa [average, hc.ne'] using div_le_div_of_nonneg_right hs hc.le

theorem full_probe_density_lower (C : Finset U) (D : Finset W)
    (draw : U → W → I) (attempt : I → Attempt V) (delta : U → ℚ)
    (hchild : ∀ u ∈ C, delta u ≤ Prob.probability D (successSeeds D (draw u) attempt)) :
    average C delta ≤ Prob.probability (C ×ˢ D)
      (successSeeds (C ×ˢ D) (fun uv => draw uv.1 uv.2) attempt) := by
  rw [full_probe_rate_eq_average]
  exact average_mono C _ _ hchild

/-- A uniform child bound on a good subset yields the coarser alpha*delta rate. -/
theorem good_call_density_lower (C : Finset U) (D : Finset W)
    (B : Finset U) (hB : B ⊆ C) (draw : U → W → I) (attempt : I → Attempt V)
    (alpha delta : ℚ) (hd : 0 ≤ delta) (ha : alpha ≤ B.card / (C.card : ℚ))
    (hchild : ∀ u ∈ B, delta ≤ Prob.probability D (successSeeds D (draw u) attempt)) :
    alpha * delta ≤ Prob.probability (C ×ˢ D)
      (successSeeds (C ×ˢ D) (fun uv => draw uv.1 uv.2) attempt) := by
  have hl := Finset.sum_le_sum hchild
  have he := Finset.sum_le_sum_of_subset_of_nonneg hB
    (fun u _ _ => CryptoBulletproofsIPATreeProbabilityContract.probability_nonnegative D
      (successSeeds D (draw u) attempt))
  have hh := div_le_div_of_nonneg_right (hl.trans he) (Nat.cast_nonneg (α := ℚ) C.card)
  rw [full_probe_rate_eq_average]
  calc alpha * delta ≤ (B.card / (C.card : ℚ)) * delta := mul_le_mul_of_nonneg_right ha hd
       _ ≤ _ := by simpa [average, Finset.sum_const, nsmul_eq_mul, div_mul_eq_mul_div] using hh

/-- Independent child seed blocks preserve the call-key law, not uniformity of its image. -/
theorem full_probe_class_mass_eq (C : Finset U) (D : Finset W) (hD : D.Nonempty)
    (draw : U → W → I) (label : I → K) (callKey : U → K)
    (hkey : ∀ u v, label (draw u v) = callKey u) (a : K) :
    Prob.probability (C ×ˢ D) (classSeeds (C ×ˢ D) (fun uv => draw uv.1 uv.2) label a) =
      Prob.probability C (C.filter fun u => callKey u = a) := by
  have hd : (D.card : ℚ) ≠ 0 := by exact_mod_cast hD.card_ne_zero
  rw [show classSeeds (C ×ˢ D) (fun uv => draw uv.1 uv.2) label a =
      (C.filter fun u => callKey u = a) ×ˢ D by ext uv; simp [classSeeds, hkey]; tauto]
  have hs : (C.filter fun u => callKey u = a) ×ˢ D ⊆ C ×ˢ D :=
    Finset.product_subset_product (Finset.filter_subset _ _) (Finset.Subset.refl _)
  simp only [Prob.probability, Finset.inter_eq_left.mpr hs,
    Finset.inter_eq_left.mpr (Finset.filter_subset _ _), Finset.card_product, Nat.cast_mul]
  exact mul_div_mul_right _ _ hd

/-- Average child guarantees feed the unchanged actual collector and epsilon217. -/
theorem averaged_collect_probability_lower (n : ℕ) (C : Finset U) (hC : C.Nonempty)
    (D : Finset W) (hD : D.Nonempty) (draw : U → W → I)
    (label : I → K) (key : V → K) (attempt : I → Attempt V)
    (hc : KeyCoherent label key attempt) (callKey : U → K)
    (hkey : ∀ u v, label (draw u v) = callKey u)
    (delta : U → ℚ) (hd : ∀ u ∈ C, 0 ≤ delta u ∧ delta u ≤ 1)
    (hchild : ∀ u ∈ C, delta u ≤ Prob.probability D (successSeeds D (draw u) attempt))
    (beta : ℚ) (hb : 0 ≤ beta)
    (hclass : ∀ a, Prob.probability C (C.filter fun u => callKey u = a) ≤ beta) (T : ℕ) :
    quotaLower n (fun j => max 0 (average C delta - (j : ℚ) * beta)) T 0 ≤
      Prob.probability (Product.productTapes (C ×ˢ D) T)
        ((Product.productTapes (C ×ˢ D) T).filter fun w =>
          (collect n label key attempt (iidSchedule (fun uv => draw uv.1 uv.2) w)).value.isSome)
              := by
  apply iid_collect_probability_lower n (C ×ˢ D) (hC.product hD) _ label key attempt hc
    (average C delta) beta (average_bounds C hC delta hd).1 (average_bounds C hC delta hd).2 hb
  · exact full_probe_density_lower C D draw attempt delta hchild
  · intro a
    rw [full_probe_class_mass_eq C D hD draw label callKey hkey a]
    exact hclass a
end Finite

/-- Positive rates at all required states and enough trials imply a positive bound. -/
theorem quota_positive (n : ℕ) (p : ℕ → ℚ)
    (hp : ∀ j < n, 0 < p j ∧ p j ≤ 1) (T j : ℕ) (hT : n ≤ j + T) :
    0 < quotaLower n p T j := by
  induction T generalizing j with
  | zero => simp only [Nat.add_zero] at hT; simp [quotaLower, hT]
  | succ T ih =>
    by_cases h : n ≤ j
    · rw [quota_full n p (T + 1) j h]; norm_num
    have hj : j < n := by omega
    have ht := ih (j + 1) (by omega)
    have hn := (quota_bounds n p (fun i hi => ⟨(hp i hi).1.le,(hp i hi).2⟩) T j).1
    rw [quotaLower, if_neg h]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr (hp j hj).2) hn)
      (mul_pos (hp j hj).1 ht)

/-- Sufficient positivity threshold for this conservative bound.
Not a necessary condition for actual success. -/
theorem linear_quota_positive (n T : ℕ) (hn : 0 < n) (hT : n ≤ T)
    (d beta : ℚ) (hd : d ≤ 1) (hb : 0 ≤ beta)
    (hgap : ((n - 1 : ℕ) : ℚ) * beta < d) :
    0 < quotaLower n (fun j => max 0 (d - (j : ℚ) * beta)) T 0 := by
  apply quota_positive n _ _ T 0 (by omega)
  intro j hj
  have hjn : (j : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by exact_mod_cast (show j ≤ n - 1 by omega)
  have hm := mul_le_mul_of_nonneg_right hjn hb
  constructor
  · exact lt_max_of_lt_right (by linarith)
  · exact max_le (by norm_num) (le_trans (sub_le_self d (mul_nonneg (Nat.cast_nonneg _) hb)) hd)

section Snapshots
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
  [DecidableEq A] {Ω S U W : Type} [DecidableEq U] [DecidableEq W] {k : ℕ}

/-- The child event is evaluated at the observed snapshot, not merely its Statement. -/
theorem round_attempt_child_event (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (hs : ReachableSnapshot m s) (st : Statement q A (k + 1)) (lr : RoundMessages A)
    (x : (ZMod q)ˣ) (o : Observation m s (.inner k x))
    (ho : query m s (.inner k x) = some o) (ps : IPASchedule q k) :
    (roundAttempt m s hs st lr (x,ps)).value.isSome =
      (acquireTree m o.after (o.reachable hs) o.packet (child_statement st lr x) ps).value.isSome
          := by
  simp [roundAttempt, ho, restore]

theorem eta_attempt_child_event (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A) (e t : ZMod q)
    (eta : (ZMod q)ˣ) (o : Observation m s (.binding eta))
    (ho : query m s (.binding eta) = some o) (ps : IPASchedule q k) :
    (etaAttempt p m s hs ann e t (eta,ps)).value.isSome =
      (acquireTree m o.after (o.reachable hs) o.packet
        (P.toIPA (C.responseClaim p ann e t) eta) ps).value.isSome := by
  simp [etaAttempt, ho, restore]

/-- Exact conditional child laws, including deterministic abort. -/
def roundChildRate (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (hs : ReachableSnapshot m s) (st : Statement q A (k + 1)) (lr : RoundMessages A)
    (D : Finset W) (x : (ZMod q)ˣ) (child : W → IPASchedule q k) : ℚ :=
  match query m s (.inner k x) with
  | none => 0
  | some o => Prob.probability D (D.filter fun v =>
      (acquireTree m o.after (o.reachable hs) o.packet (child_statement st lr x) (child
          v)).value.isSome)

def etaChildRate (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A) (e t : ZMod q)
    (D : Finset W) (eta : (ZMod q)ˣ) (child : W → IPASchedule q k) : ℚ :=
  match query m s (.binding eta) with
  | none => 0
  | some o => Prob.probability D (D.filter fun v =>
      (acquireTree m o.after (o.reachable hs) o.packet
        (P.toIPA (C.responseClaim p ann e t) eta) (child v)).value.isSome)

/-- Unlike the parent full-probe premise, the hypotheses concern the child collector
with its own law after an actual primitive observation. -/
theorem round_density_lower (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (hs : ReachableSnapshot m s) (st : Statement q A (k + 1)) (lr : RoundMessages A)
    (C : Finset U) (D : Finset W) (call : U → (ZMod q)ˣ)
    (child : U → W → IPASchedule q k) (delta : U → ℚ)
    (hchild : ∀ u ∈ C, delta u ≤ roundChildRate m s hs st lr D (call u) (child u)) :
    average C delta ≤ Prob.probability (C ×ˢ D) (successSeeds (C ×ˢ D)
      (fun uv => (call uv.1, child uv.1 uv.2)) (roundAttempt m s hs st lr)) := by
  refine full_probe_density_lower C D (fun u v => (call u,child u v))
    (roundAttempt m s hs st lr) delta ?_
  intro u hu
  have he : roundChildRate m s hs st lr D (call u) (child u) =
      Prob.probability D (successSeeds D (fun v => (call u,child u v)) (roundAttempt m s hs st
          lr)) := by
    unfold roundChildRate
    split <;> rename_i h
    · simp [roundAttempt, restore, h, successSeeds, Prob.probability]
    · simp [roundAttempt, restore, h, successSeeds]
  rw [← he]
  exact hchild u hu

theorem eta_density_lower (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A) (e t : ZMod q)
    (C : Finset U) (D : Finset W) (call : U → (ZMod q)ˣ)
    (child : U → W → IPASchedule q k) (delta : U → ℚ)
    (hchild : ∀ u ∈ C, delta u ≤ etaChildRate p m s hs ann e t D (call u) (child u)) :
    average C delta ≤ Prob.probability (C ×ˢ D) (successSeeds (C ×ˢ D)
      (fun uv => (call uv.1, child uv.1 uv.2)) (etaAttempt p m s hs ann e t)) := by
  refine full_probe_density_lower C D (fun u v => (call u,child u v))
    (etaAttempt p m s hs ann e t) delta ?_
  intro u hu
  have he : etaChildRate p m s hs ann e t D (call u) (child u) =
      Prob.probability D (successSeeds D (fun v => (call u,child u v)) (etaAttempt p m s hs ann e
          t)) := by
    unfold etaChildRate
    split <;> rename_i h
    · simp [etaAttempt, restore, h, successSeeds, Prob.probability]
    · simp [etaAttempt, restore, h, successSeeds]
  rw [← he]
  exact hchild u hu

/-- Post-e rate: abort, unexpected packet and false scalar equation contribute zero. -/
def outerChildRate (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A)
    (D : Finset W) (e : ZMod q) (child : W → EtaSchedule q k) : ℚ :=
  match query m s (.outer e) with
  | none => 0
  | some o => match o.packet with
    | .scalar t z => if C.scalarCheck p ann e t z then
        Prob.probability D (D.filter fun v => (collect 2 Prod.fst (fun w => w.1)
          (etaAttempt p m o.after (o.reachable hs) ann e t) (child v)).value.isSome) else 0
    | _ => 0

set_option backward.isDefEq.respectTransparency false in
theorem outer_child_rate_eq (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A)
    (D : Finset W) (e : ZMod q) (child : W → EtaSchedule q k) :
    outerChildRate p m s hs ann D e child = Prob.probability D
      (successSeeds D (fun v => (e,child v)) (fun pr => acquireNode p m s hs ann pr.1 pr.2)) := by
  unfold outerChildRate
  split
  · rename_i h
    simp [successSeeds, acquireNode, restore, h, Prob.probability]
  · rename_i o ho
    split
    · rename_i t z ha
      split_ifs with hv
      · congr 1
        apply Finset.filter_congr
        intro v _
        change _ ↔ (acquireNode p m s hs ann e (child v)).value.isSome = true
        rw [node_collect_event p m s hs ann e t z o ho ha hv]
      · have hf (v : W) : (acquireNode p m s hs ann e (child v)).value.isSome = false := by
          unfold acquireNode
          simp only [restore, ho]
          split
          · rename_i t' z' he
            obtain ⟨ht,hz⟩ := Packet.scalar.inj (he.symm.trans ha)
            subst t'; subst z'
            simp only [dif_neg hv]
            rfl
          · rename_i hbad
            exact False.elim (hbad t z ha)
        simp [successSeeds, hf, Prob.probability]
    · rename_i hbad
      have hf (v : W) : (acquireNode p m s hs ann e (child v)).value.isSome = false := by
        unfold acquireNode
        simp only [restore, ho]
        rfl
      simp [successSeeds, hf, Prob.probability]

theorem outer_density_lower (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A)
    (C : Finset U) (D : Finset W) (call : U → ZMod q)
    (child : U → W → EtaSchedule q k) (delta : U → ℚ)
    (hchild : ∀ u ∈ C, delta u ≤ outerChildRate p m s hs ann D (call u) (child u)) :
    average C delta ≤ Prob.probability (C ×ˢ D) (successSeeds (C ×ˢ D)
      (fun uv => (call uv.1,child uv.1 uv.2)) (fun pr => acquireNode p m s hs ann pr.1 pr.2)) := by
  refine full_probe_density_lower C D (fun u v => (call u,child u v))
    (fun pr => acquireNode p m s hs ann pr.1 pr.2) delta ?_
  intro u hu
  rw [← outer_child_rate_eq]
  exact hchild u hu

/-- End-to-end outer quota bound with density derived from post-e child laws. -/
theorem averaged_acquisition_probability_lower (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (o : Observation m (initialSnapshot m) .commit) (ann : F.Announcement A)
    (ho : query m (initialSnapshot m) .commit = some o) (ha : o.packet = .announcement ann)
    (C : Finset U) (hC : C.Nonempty) (D : Finset W) (hD : D.Nonempty)
    (call : U → ZMod q) (child : U → W → EtaSchedule q k) (delta : U → ℚ)
    (hd : ∀ u ∈ C, 0 ≤ delta u ∧ delta u ≤ 1)
    (hchild : ∀ u ∈ C, delta u ≤ outerChildRate p m o.after (o.reachable .initial) ann D (call u)
        (child u))
    (beta : ℚ) (hb : 0 ≤ beta)
    (hclass : ∀ a, Prob.probability C (C.filter fun u => call u = a) ≤ beta) (T : ℕ) :
    quotaLower 3 (fun j => max 0 (average C delta - (j : ℚ) * beta)) T 0 ≤
      Prob.probability (Product.productTapes (C ×ˢ D) T)
        ((Product.productTapes (C ×ˢ D) T).filter fun w =>
          (acquireCompressedFork p m (iidSchedule (fun uv => (call uv.1,child uv.1 uv.2))
              w)).outcome.isOk) := by
  apply iid_acquisition_probability_lower p m o ann ho ha (C ×ˢ D) (hC.product hD) _
    (average C delta) beta (average_bounds C hC delta hd).1 (average_bounds C hC delta hd).2 hb
  · exact outer_density_lower p m o.after (o.reachable .initial) ann C D call child delta hchild
  · intro a
    rw [full_probe_class_mass_eq C D hD (fun u v => (call u,child u v)) Prod.fst call (fun _ _ =>
        rfl) a]
    exact hclass a
end Snapshots

structure CryptoHiddenScalarForkLocalDensityContractSuite : Prop where
  averaging : ∀ (U W I V : Type) [DecidableEq U] [DecidableEq W]
    (C : Finset U) (D : Finset W) (draw : U → W → I) (attempt : I → Attempt V),
    Prob.probability (C ×ˢ D) (successSeeds (C ×ˢ D) (fun uv => draw uv.1 uv.2) attempt) =
      average C (fun u => Prob.probability D (successSeeds D (draw u) attempt))
  density : ∀ (U W I V : Type) [DecidableEq U] [DecidableEq W]
    (C : Finset U) (D : Finset W) (draw : U → W → I) (attempt : I → Attempt V)
    (delta : U → ℚ),
    (∀ u ∈ C, delta u ≤ Prob.probability D (successSeeds D (draw u) attempt)) →
    average C delta ≤ Prob.probability (C ×ˢ D)
      (successSeeds (C ×ˢ D) (fun uv => draw uv.1 uv.2) attempt)
  positivity : ∀ n T : ℕ, 0 < n → n ≤ T → ∀ d beta : ℚ, d ≤ 1 → 0 ≤ beta →
    ((n - 1 : ℕ) : ℚ) * beta < d → 0 < quotaLower n (fun j => max 0 (d - (j : ℚ) * beta)) T 0

theorem verification_suite : CryptoHiddenScalarForkLocalDensityContractSuite where
  averaging := fun _ _ _ _ _ _ => full_probe_rate_eq_average
  density := fun _ _ _ _ _ _ => full_probe_density_lower
  positivity := linear_quota_positive
end CryptoHiddenScalarForkLocalDensityContract
