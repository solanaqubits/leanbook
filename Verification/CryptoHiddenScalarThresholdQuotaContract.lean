/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarSinglePathContract

/-! Threshold transfer from actual single-path acceptance to the existing recursive
quota bound. Fixed tape, finite independent microseeds, original class masses.
No new acquirer, extractor, early-stop policy, ROM or complexity claim. -/
namespace CryptoHiddenScalarThresholdQuotaContract
set_option backward.isDefEq.respectTransparency false
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkScheduleProgressContract
open CryptoHiddenScalarForkLocalDensityContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarSinglePathContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction

/-- Monotonicity in the probability profile, not merely the retained count. -/
theorem quota_profile_mono (n T j : ℕ) (p p' : ℕ → ℚ)
    (hp : ∀ i < n, 0 ≤ p i) (hle : ∀ i < n, p i ≤ p' i)
    (hp' : ∀ i < n, p' i ≤ 1) :
    quotaLower n p T j ≤ quotaLower n p' T j := by
  induction T generalizing j with
  | zero => rfl
  | succ T ih =>
    by_cases h : n ≤ j
    · simp [quota_full, h]
    have hj : j < n := by omega
    have h0 := hp j hj
    have h1 := (hle j hj).trans (hp' j hj)
    have h2 := hle j hj
    have hs := ih j
    have hc := ih (j+1)
    have hm := quota_step_mono n p' (fun i hi => ⟨(hp i hi).trans (hle i hi),hp' i hi⟩) T j
    rw [quotaLower, if_neg h, quotaLower, if_neg h]
    nlinarith [mul_nonneg (show 0 ≤ 1-p j by linarith) (sub_nonneg.mpr hs),
      mul_nonneg h0 (sub_nonneg.mpr hc), mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr hm)]

theorem quota_density_mono (n T : ℕ) (d₀ d₁ beta : ℚ)
    (_hd₀ : 0 ≤ d₀) (hdd : d₀ ≤ d₁) (hd₁ : d₁ ≤ 1) (hb : 0 ≤ beta) :
    quota n T d₀ beta ≤ quota n T d₁ beta := by
  apply quota_profile_mono
  · intro i _; exact le_max_left _ _
  · intro i _; exact max_le_max (le_refl _) (sub_le_sub_right hdd _)
  · intro i _
    exact max_le (by norm_num) ((sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hb)).trans hd₁)

/-- Only the finite prefix down to the leaf is used. Root may equal one;
all thresholds used as child cutoffs are strictly below one. -/
structure ThresholdProfile where
  value : ℕ → ℚ
  pos : ∀ i, 0 < value i
  le_one : ∀ i, value i ≤ 1
  child_lt : ∀ i, value (i+1) < 1

def ThresholdProfile.tail (h : ThresholdProfile) : ThresholdProfile where
  value := fun i => h.value (i+1)
  pos := fun i => h.pos (i+1)
  le_one := fun i => h.le_one (i+1)
  child_lt := fun i => h.child_lt (i+1)

def heavyMass (a theta : ℚ) : ℚ := max 0 ((a-theta)/(1-theta))

theorem heavyMass_range (a theta : ℚ) (ha : a ≤ 1) (ht : theta < 1) :
    0 ≤ heavyMass a theta ∧ heavyMass a theta ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 1-theta)).mpr
  linarith

/-- Heavy children retain their original microseed weights; no conditional resampling. -/
theorem threshold_average_lower {U : Type} [Fintype U] [Nonempty U]
    (a b : U → ℚ) (tau theta c : ℚ) (ht : theta < 1) (hc : 0 ≤ c)
    (ha : ∀ i, a i ≤ 1) (hb : ∀ i, 0 ≤ b i)
    (hav : tau ≤ average Finset.univ a)
    (hchild : ∀ i, theta ≤ a i → c ≤ b i) :
    heavyMass tau theta * c ≤ average Finset.univ b := by
  classical
  have h := Heavy.heavy_prefix_fraction_lower Finset.univ Finset.univ_nonempty a theta ht
    (fun i _ => ha i)
  have htpos : 0 < 1-theta := by linarith
  have hdiv : (tau-theta)/(1-theta) ≤ (average Finset.univ a-theta)/(1-theta) :=
    div_le_div_of_nonneg_right (sub_le_sub_right hav _) htpos.le
  have hmass : heavyMass tau theta ≤ Heavy.heavyFraction Finset.univ a theta := by
    apply max_le
    · unfold Heavy.heavyFraction; positivity
    · exact hdiv.trans h
  have havg := CryptoBulletproofsIPAFiniteForkingProbabilityContract.average_lower_on_heavy
    Finset.univ Finset.univ_nonempty a b theta c (fun i _ => hb i)
    (fun i hi => hchild i (Finset.mem_filter.mp hi).2)
  exact (mul_le_mul_of_nonneg_right hmass hc).trans havg


section Rates
variable {U : Type} [Fintype U] [DecidableEq U]
def eventRate (f : U → Bool) : ℚ :=
  Prob.probability (Finset.univ : Finset U) (Finset.univ.filter fun u => f u)

theorem eventRate_range [Nonempty U] (f : U → Bool) :
    0 ≤ eventRate f ∧ eventRate f ≤ 1 :=
  ⟨CryptoBulletproofsIPATreeProbabilityContract.probability_nonnegative _ _,
    CryptoBulletproofsIPATreeProbabilityContract.probability_le_one _ _ Finset.univ_nonempty⟩

@[simp] theorem eventRate_false : eventRate (fun _ : U => false) = 0 := by
  simp [eventRate, Prob.probability]

@[simp] theorem eventRate_true [Nonempty U] : eventRate (fun _ : U => true) = 1 := by
  simp [eventRate, Prob.probability, Fintype.card_ne_zero]

theorem eventRate_guard (g : Bool) (f : U → Bool) :
    eventRate (fun u => g && f u) = if g then eventRate f else 0 := by
  cases g <;> simp
end Rates

instance pathSeedNonempty {q : ℕ} {S : Type} : {d : ℕ} → (p : TreePlan q S d) → Nonempty
  (PathSeed p)
  | _, .leaf => ⟨()⟩
  | _, .node law _ child => ⟨(⟨0,law.size_pos⟩, Classical.choice (pathSeedNonempty child))⟩

variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
  [DecidableEq A] {Ω S : Type} {k : ℕ}

def treePathEvent (p : TreePlan q S k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (msg : Packet q A)
    (st : Statement q A k) (w : PathSeed p) : Bool :=
  (runIPA m p s hs msg st w).any (fun r => r.val.accepted)

def treePathRate (p : TreePlan q S k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (msg : Packet q A)
    (st : Statement q A k) : ℚ := eventRate (treePathEvent p m s hs msg st)

theorem tree_path_rate_range (p : TreePlan q S k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (msg : Packet q A) (st : Statement q A k) :
    0 ≤ treePathRate p m s hs msg st ∧ treePathRate p m s hs msg st ≤ 1 :=
  eventRate_range _

theorem tree_path_rate_leaf (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (msg : Packet q A) (st : Statement q A 0) :
    treePathRate .leaf m s hs msg st = TreePlan.bound .leaf m s msg st := by
  cases msg with
  | leaf a b =>
    change eventRate (fun _ : Unit => decide (st.P = a • st.G 0 + b • st.H 0 + (a*b) • st.U)) =
      if ValidAcceptingTree st (.leaf st a b) then 1 else 0
    simp only [ValidAcceptingTree, true_and]
    split_ifs with h <;> simp [h]
  | _ => change eventRate (fun _ : Unit => false) = 0; exact eventRate_false

set_option backward.isDefEq.respectTransparency false in
/-- Exact average over calls, with no child access on a failed primitive query. -/
theorem tree_path_rate_node (m : AdversaryModel q A Ω S)
    (law : CallLaw (Snapshot q S) (ZMod q)ˣ (ZMod q) (fun x => (x : ZMod q) ^ 2))
    (T : ℕ) (child : TreePlan q S k) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (msg : Packet q A) (st : Statement q A (k + 1)) :
    treePathRate (.node law T child) m s hs msg st = match msg with
      | .round lr => average Finset.univ (fun i => (query m s (.inner k (law.call s i))).elim 0
          (fun o => treePathRate child m o.after (o.reachable hs) o.packet
            (child_statement st lr (law.call s i))))
      | _ => 0 := by
  cases msg <;> try { simp [treePathRate, treePathEvent, runIPA, eventRate, Prob.probability] }
  rename_i lr
  have h := product_event_average (Finset.univ : Finset (Fin law.size))
    (Finset.univ : Finset (PathSeed child))
    (fun i v => treePathEvent (.node law T child) m s hs (.round lr) st (i,v))
  rw [show treePathRate (.node law T child) m s hs (.round lr) st =
      average Finset.univ (fun i => eventRate (fun v =>
        treePathEvent (.node law T child) m s hs (.round lr) st (i,v))) by
    convert h using 1 <;> simp only [treePathRate,eventRate,Finset.univ_product_univ,Prod.mk.eta]
    all_goals congr! 4]
  congr 1
  funext i
  cases hq : query m s (.inner k (law.call s i)) with
  | none =>
    have he : (fun v => treePathEvent (.node law T child) m s hs (.round lr) st (i,v)) = fun _
      => false := by
      funext v
      unfold treePathEvent
      rw [runIPA.eq_def]
      simp [hq]
    rw [he]
    simp
  | some o =>
    unfold treePathRate
    congr 1
    funext v
    unfold treePathEvent
    rw [runIPA.eq_def m (k + 1)]
    simp only [hq]
    cases runIPA m child o.after (o.reachable hs) o.packet (child_statement st lr (law.call s
      i)) v <;> rfl


/-- Event wrappers use the existing runner; they do not replace the raw execution. -/
def etaPathEvent (p : EtaPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (ann : F.Announcement A) (e t : ZMod q) (w : Fin p.law.size × PathSeed p.tree) : Bool :=
  match query m s (.binding (p.law.call s w.1)) with
  | none => false
  | some o => treePathEvent p.tree m o.after (o.reachable hs) o.packet
      (P.toIPA (C.responseClaim claim ann e t) (p.law.call s w.1)) w.2

def etaPathRate (p : EtaPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (ann : F.Announcement A) (e t : ZMod q) : ℚ :=
  eventRate (etaPathEvent p claim m s hs ann e t)

def outerPathEvent (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (ann : F.Announcement A) (w : SinglePathSeed p) : Bool :=
  match query m s (.outer (p.law.call s w.1)) with
  | none => false
  | some o => match o.packet with
    | .scalar t z => decide (C.scalarCheck claim ann (p.law.call s w.1) t z) &&
        etaPathEvent p.eta claim m o.after (o.reachable hs) ann (p.law.call s w.1) t w.2
    | _ => false

def outerPathRate (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (ann : F.Announcement A) : ℚ := eventRate (outerPathEvent p claim m s hs ann)

set_option backward.isDefEq.respectTransparency false in
theorem eta_path_rate_average (p : EtaPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (ann : F.Announcement A) (e t : ZMod q) :
    etaPathRate p claim m s hs ann e t = average Finset.univ (fun i =>
      (query m s (.binding (p.law.call s i))).elim 0 (fun o =>
        treePathRate p.tree m o.after (o.reachable hs) o.packet
          (P.toIPA (C.responseClaim claim ann e t) (p.law.call s i)))) := by
  have h := product_event_average (Finset.univ : Finset (Fin p.law.size))
    (Finset.univ : Finset (PathSeed p.tree)) (fun i v => etaPathEvent p claim m s hs ann e t (i,v))
  rw [show etaPathRate p claim m s hs ann e t = average Finset.univ
      (fun i => eventRate (fun v => etaPathEvent p claim m s hs ann e t (i,v))) by
    simpa only [etaPathRate,eventRate,Finset.univ_product_univ,Prod.mk.eta] using h]
  congr 1
  funext i
  cases hq : query m s (.binding (p.law.call s i)) <;>
    simp [etaPathEvent,hq,treePathRate]

set_option backward.isDefEq.respectTransparency false in
theorem outer_path_rate_average (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (ann : F.Announcement A) :
    outerPathRate p claim m s hs ann = average Finset.univ (fun i =>
      (query m s (.outer (p.law.call s i))).elim 0 (fun o => match o.packet with
        | .scalar t z => if C.scalarCheck claim ann (p.law.call s i) t z then
            etaPathRate p.eta claim m o.after (o.reachable hs) ann (p.law.call s i) t else 0
        | _ => 0)) := by
  have h := product_event_average (Finset.univ : Finset (Fin p.law.size))
    (Finset.univ : Finset (Fin p.eta.law.size × PathSeed p.eta.tree))
    (fun i v => outerPathEvent p claim m s hs ann (i,v))
  rw [show outerPathRate p claim m s hs ann = average Finset.univ
      (fun i => eventRate (fun v => outerPathEvent p claim m s hs ann (i,v))) by
    simpa only [outerPathRate,eventRate,Finset.univ_product_univ,Prod.mk.eta] using h]
  congr 1
  funext i
  cases hq : query m s (.outer (p.law.call s i)) with
  | none => simp [outerPathEvent,hq]
  | some o =>
    simp only [outerPathEvent,hq,Option.elim_some]
    cases o.packet <;> try { simp }
    simp only
    split_ifs with h <;> simp [h,etaPathRate]

set_option backward.isDefEq.respectTransparency false in
/-- Equality concerns acceptance, not early stopping of transcript production. -/
theorem execute_event (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (w : SinglePathSeed p) :
    (execute p claim m w).any (fun r => r.accepted) =
      (query m (initialSnapshot m) .commit).elim false (fun c => match c.packet with
        | .announcement ann => outerPathEvent p claim m c.after (c.reachable .initial) ann w
        | _ => false) := by
  simp only [execute,executeCertified,bind, Option.any_map,
    Option.any_bind]
  cases hc : query m (initialSnapshot m) .commit with
  | none => rfl
  | some c =>
    rcases c with ⟨cp,cm,cu,ce⟩
    simp only [Option.any_some, Option.elim_some]
    cases cp <;> try rfl
    rename_i ann
    simp only [Option.any_bind, Function.comp_apply]
    unfold outerPathEvent
    cases he : query m _ (.outer (p.law.call _ w.1)) with
    | none => rfl
    | some o =>
      rcases o with ⟨op,om,ou,oe⟩
      simp only [Option.any_some]
      cases op <;> try rfl
      rename_i t z
      simp only [Option.any_bind, Function.comp_apply]
      unfold etaPathEvent treePathEvent
      cases hb : query m _ (.binding (p.eta.law.call _ w.2.1)) with
      | none => simp
      | some b =>
        simp only [Option.any_some]
        simp only [Option.any_bind, Function.comp_apply, pure]
        have hh {X : Type} (o : Option X) (g : Bool) (f : X → Bool) :
            o.any (fun a => g && f a) = (g && o.any f) := by cases o <;> simp
        exact hh _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem acceptance_rate_local (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) :
    acceptanceRate p claim m = (query m (initialSnapshot m) .commit).elim 0 (fun c =>
      match c.packet with
      | .announcement ann => outerPathRate p claim m c.after (c.reachable .initial) ann
      | _ => 0) := by
  have he : acceptanceRate p claim m = eventRate (fun w => (execute p claim m w).any (fun r =>
    r.accepted)) := by
    simp [acceptanceRate,eventRate,AcceptedRun,Option.any_eq_true]
  rw [he]
  simp only [execute_event]
  cases hc : query m (initialSnapshot m) .commit with
  | none => simp
  | some c => cases hp : c.packet <;> simp [hp,outerPathRate]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical post-e row keeps the prefix's scalar-check indicator. -/
theorem continuation_rate_eq_local (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S)
    (c : Observation m (initialSnapshot m) .commit) (ann : F.Announcement A)
    (hc : query m (initialSnapshot m) .commit = some c) (ha : c.packet = .announcement ann)
    (i : Fin p.law.size) :
    continuationRate p claim m (afterESplit p) i =
      (query m c.after (.outer (p.law.call c.after i))).elim 0 (fun o => match o.packet with
        | .scalar t z => if C.scalarCheck claim ann (p.law.call c.after i) t z then
            etaPathRate p.eta claim m o.after (o.reachable (c.reachable .initial)) ann
              (p.law.call c.after i) t else 0
        | _ => 0) := by
  have he : continuationRate p claim m (afterESplit p) i =
      eventRate (fun v => (execute p claim m (i,v)).any (fun r => r.accepted)) := by
    simp [continuationRate,afterESplit,eventRate,AcceptedRun,Option.any_eq_true]
  rw [he]
  simp only [execute_event,hc,Option.elim_some,ha,outerPathEvent]
  cases hq : query m c.after (.outer (p.law.call c.after i)) with
  | none => simp
  | some o =>
    simp only [Option.elim_some]
    cases o.packet <;> try { exact eventRate_false }
    rename_i t z
    dsimp only
    by_cases hv : C.scalarCheck claim ann (p.law.call c.after i) t z
    · simp only [hv,decide_true,Bool.true_and,if_true]; rfl
    · simp only [hv,decide_false,Bool.false_and,if_false]; exact eventRate_false



/-- Coarse density transferred from heavy children, under the unchanged call law. -/
def thresholdDensity (h : ThresholdProfile) (b : ℚ) : ℚ :=
  heavyMass (h.value 0) (h.value 1) * b

def thresholdStep (h : ThresholdProfile) (n T : ℕ) (beta b : ℚ) : ℚ :=
  quota n T (thresholdDensity h b) beta

theorem threshold_density_range (h : ThresholdProfile) (b : ℚ) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ thresholdDensity h b ∧ thresholdDensity h b ≤ 1 := by
  have hm := heavyMass_range (h.value 0) (h.value 1) (h.le_one 0) (h.child_lt 0)
  exact ⟨mul_nonneg hm.1 hb.1, (mul_le_mul_of_nonneg_right hm.2 hb.1).trans (by simpa using hb.2)⟩

theorem threshold_step_range (h : ThresholdProfile) (n T : ℕ) (beta b : ℚ)
    (hbeta : 0 ≤ beta) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ thresholdStep h n T beta b ∧ thresholdStep h n T beta b ≤ 1 :=
  quota_range _ _ _ _ (threshold_density_range h b hb) hbeta

theorem threshold_step_le {U : Type} [Fintype U] [Nonempty U]
    (h : ThresholdProfile) (n T : ℕ) (beta b : ℚ) (hbeta : 0 ≤ beta)
    (hb : 0 ≤ b ∧ b ≤ 1) (a delta : U → ℚ)
    (ha : ∀ i, a i ≤ 1) (hd : ∀ i, 0 ≤ delta i ∧ delta i ≤ 1)
    (hav : h.value 0 ≤ average Finset.univ a)
    (hchild : ∀ i, h.value 1 ≤ a i → b ≤ delta i) :
    thresholdStep h n T beta b ≤ quota n T (average Finset.univ delta) beta := by
  apply quota_density_mono
  · exact (threshold_density_range h b hb).1
  · exact threshold_average_lower a delta _ _ _ (h.child_lt 0) hb.1 ha (fun i => (hd i).1) hav
      hchild
  · exact (average_bounds _ Finset.univ_nonempty _ (fun i _ => hd i)).2
  · exact hbeta

/-- Computed only from thresholds, budgets and class caps; not supplied child success. -/
def treeThresholdBound : {d : ℕ} → TreePlan q S d → ThresholdProfile → ℚ
  | _, .leaf, _ => 1
  | _, .node law T child, h => thresholdStep h 4 T law.beta (treeThresholdBound child h.tail)

omit [Fact q.Prime] in
theorem tree_threshold_range (p : TreePlan q S k) (h : ThresholdProfile) :
    0 ≤ treeThresholdBound p h ∧ treeThresholdBound p h ≤ 1 := by
  induction p generalizing h with
  | leaf => norm_num [treeThresholdBound]
  | node law T child ih => exact threshold_step_range h 4 T law.beta _ law.beta_nonneg (ih h.tail)

set_option backward.isDefEq.respectTransparency false in
/-- Induction discharges every internal child premise from actual leaf acceptance. -/
theorem tree_threshold_le (p : TreePlan q S k) (h : ThresholdProfile)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (msg : Packet q A) (st : Statement q A k)
    (hacc : h.value 0 ≤ treePathRate p m s hs msg st) :
    treeThresholdBound p h ≤ p.bound m s msg st := by
  induction p generalizing h s msg with
  | leaf =>
    rw [tree_path_rate_leaf] at hacc
    have ht := h.pos 0
    cases msg <;> simp only [TreePlan.bound,treeThresholdBound] at *
    all_goals try { linarith }
    split_ifs at * <;> linarith
  | @node d law T child ih =>
    rw [tree_path_rate_node] at hacc
    have ht := h.pos 0
    cases msg <;> try { simp only at hacc; exact False.elim (by linarith) }
    rename_i lr
    let a := fun i => (query m s (.inner d (law.call s i))).elim (0 : ℚ)
      (fun o => treePathRate child m o.after (o.reachable hs) o.packet (child_statement st lr
        (law.call s i)))
    let delta := fun i => (query m s (.inner d (law.call s i))).elim (0 : ℚ)
      (fun o => child.bound m o.after o.packet (child_statement st lr (law.call s i)))
    let : Nonempty (Fin law.size) := ⟨⟨0,law.size_pos⟩⟩
    apply threshold_step_le h 4 T law.beta _ law.beta_nonneg (tree_threshold_range child
      h.tail) a delta
    · intro i
      dsimp [a]
      cases query m s (.inner d (law.call s i)) with
      | none => norm_num
      | some o => exact (tree_path_rate_range child m _ _ _ _).2
    · intro i
      dsimp [delta]
      cases query m s (.inner d (law.call s i)) with
      | none => norm_num
      | some o => exact child.bound_range m _ _ _
    · exact hacc
    · intro i hi
      dsimp [a,delta] at *
      cases hq : query m s (.inner d (law.call s i)) with
      | none => simp only [hq,Option.elim_none] at hi; exact False.elim ((h.pos 1).not_ge hi)
      | some o =>
        simp only [hq,Option.elim_some] at *
        exact ih h.tail o.after (o.reachable hs) o.packet _ hi

def etaThresholdBound (p : EtaPlan q S k) (h : ThresholdProfile) : ℚ :=
  thresholdStep h 2 p.budget p.law.beta (treeThresholdBound p.tree h.tail)

omit [Fact q.Prime] in
theorem eta_threshold_range (p : EtaPlan q S k) (h : ThresholdProfile) :
    0 ≤ etaThresholdBound p h ∧ etaThresholdBound p h ≤ 1 :=
  threshold_step_range h 2 p.budget p.law.beta _ p.law.beta_nonneg (tree_threshold_range
    p.tree h.tail)

set_option backward.isDefEq.respectTransparency false in
theorem eta_threshold_le (p : EtaPlan q S k) (h : ThresholdProfile) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (ann : F.Announcement A) (e t : ZMod q)
    (hacc : h.value 0 ≤ etaPathRate p claim m s hs ann e t) :
    etaThresholdBound p h ≤ p.bound claim m s ann e t := by
  rw [eta_path_rate_average] at hacc
  let a := fun i => (query m s (.binding (p.law.call s i))).elim (0 : ℚ)
    (fun o => treePathRate p.tree m o.after (o.reachable hs) o.packet
      (P.toIPA (C.responseClaim claim ann e t) (p.law.call s i)))
  let : Nonempty (Fin p.law.size) := ⟨⟨0,p.law.size_pos⟩⟩
  apply threshold_step_le h 2 p.budget p.law.beta _ p.law.beta_nonneg
    (tree_threshold_range p.tree h.tail) a (p.branch claim m s ann e t)
  · intro i
    dsimp [a]
    cases query m s (.binding (p.law.call s i)) with
    | none => norm_num
    | some o => exact (tree_path_rate_range p.tree m _ _ _ _).2
  · exact p.branch_range claim m s ann e t
  · exact hacc
  · intro i hi
    dsimp [a] at hi
    unfold EtaPlan.branch
    cases hq : query m s (.binding (p.law.call s i)) with
    | none => simp only [hq,Option.elim_none] at hi; exact False.elim ((h.pos 1).not_ge hi)
    | some o =>
      simp only [hq,Option.elim_some] at hi
      exact tree_threshold_le p.tree h.tail m o.after (o.reachable hs) o.packet _ hi

def protocolThresholdBound (p : ProtocolPlan q S k) (h : ThresholdProfile) : ℚ :=
  thresholdStep h 3 p.budget p.law.beta (etaThresholdBound p.eta h.tail)

omit [Fact q.Prime] in
theorem protocol_threshold_range (p : ProtocolPlan q S k) (h : ThresholdProfile) :
    0 ≤ protocolThresholdBound p h ∧ protocolThresholdBound p h ≤ 1 :=
  threshold_step_range h 3 p.budget p.law.beta _ p.law.beta_nonneg (eta_threshold_range p.eta
    h.tail)

set_option backward.isDefEq.respectTransparency false in
theorem outer_threshold_le (p : ProtocolPlan q S k) (h : ThresholdProfile)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A)
    (hacc : h.value 0 ≤ outerPathRate p claim m s hs ann) :
    protocolThresholdBound p h ≤ p.boundAt claim m s ann := by
  rw [outer_path_rate_average] at hacc
  let a := fun i => (query m s (.outer (p.law.call s i))).elim (0 : ℚ) (fun o => match o.packet with
    | .scalar t z => if C.scalarCheck claim ann (p.law.call s i) t z then
        etaPathRate p.eta claim m o.after (o.reachable hs) ann (p.law.call s i) t else 0
    | _ => 0)
  let : Nonempty (Fin p.law.size) := ⟨⟨0,p.law.size_pos⟩⟩
  apply threshold_step_le h 3 p.budget p.law.beta _ p.law.beta_nonneg
    (eta_threshold_range p.eta h.tail) a (p.branch claim m s ann)
  · intro i
    dsimp [a]
    cases hq : query m s (.outer (p.law.call s i)) with
    | none => norm_num
    | some o =>
      simp only [Option.elim_some]
      cases o.packet
      all_goals try { norm_num }
      dsimp only
      split_ifs
      · let : Nonempty (Fin p.eta.law.size) := ⟨⟨0,p.eta.law.size_pos⟩⟩
        exact (eventRate_range _).2
      · norm_num
  · exact p.branch_range claim m s ann
  · exact hacc
  · intro i hi
    dsimp [a] at hi
    unfold ProtocolPlan.branch
    cases hq : query m s (.outer (p.law.call s i)) with
    | none => simp only [hq,Option.elim_none] at hi; exact False.elim ((h.pos 1).not_ge hi)
    | some o =>
      simp only [hq,Option.elim_some] at hi
      cases hp : o.packet <;> simp only [hp] at *
      all_goals try { exact False.elim ((h.pos 1).not_ge hi) }
      split_ifs with hv
      · rw [if_pos hv] at hi
        exact eta_threshold_le p.eta h.tail claim m o.after (o.reachable hs) ann _ _ hi
      · rw [if_neg hv] at hi
        exact False.elim ((h.pos 1).not_ge hi)

set_option backward.isDefEq.respectTransparency false in
theorem acceptance_threshold_le (p : ProtocolPlan q S k) (h : ThresholdProfile)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (hacc : h.value 0 ≤ acceptanceRate p claim m) :
    protocolThresholdBound p h ≤ p.bound claim m := by
  rw [acceptance_rate_local] at hacc
  unfold ProtocolPlan.bound
  cases hc : query m (initialSnapshot m) .commit with
  | none => simp only [hc,Option.elim_none] at hacc; exact False.elim ((h.pos 0).not_ge hacc)
  | some c =>
    simp only [hc,Option.elim_some] at hacc
    cases hp : c.packet <;> simp only [hp] at *
    all_goals try { exact False.elim ((h.pos 0).not_ge hacc) }
    exact outer_threshold_le p h claim m c.after (c.reachable .initial) _ hacc

theorem threshold_acquisition_lower (p : ProtocolPlan q S k) (h : ThresholdProfile)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (hacc : h.value 0 ≤ acceptanceRate p claim m) :
    protocolThresholdBound p h ≤ Prob.probability Finset.univ
      (Finset.univ.filter fun w => (acquireCompressedFork claim m (p.decode m w)).outcome.isOk) :=
  (acceptance_threshold_le p h claim m hacc).trans (p.probability_lower claim m)

theorem threshold_positive_extracts (p : ProtocolPlan q S k) (h : ThresholdProfile)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (hacc : h.value 0 ≤ acceptanceRate p claim m) (hb : 0 < protocolThresholdBound p h) :
    ∃ w : p.Seed, ∃ f, (acquireCompressedFork claim m (p.decode m w)).outcome = .ok f ∧
      ForkProvenance m f ∧ F.ResultValid claim (C.extractCompressed claim f) :=
  p.positive_extracts claim m (hb.trans_le (acceptance_threshold_le p h claim m hacc))


set_option backward.isDefEq.respectTransparency false in
theorem tree_path_event_node (m : AdversaryModel q A Ω S)
    (law : CallLaw (Snapshot q S) (ZMod q)ˣ (ZMod q) (fun x => (x : ZMod q) ^ 2))
    (T : ℕ) (child : TreePlan q S k) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (msg : Packet q A) (st : Statement q A (k + 1)) (i : Fin law.size) (v : PathSeed child) :
    treePathEvent (.node law T child) m s hs msg st (i,v) = match msg with
    | .round lr => (query m s (.inner k (law.call s i))).elim false (fun o =>
        treePathEvent child m o.after (o.reachable hs) o.packet (child_statement st lr
          (law.call s i)) v)
    | _ => false := by
  unfold treePathEvent
  rw [runIPA.eq_def]
  cases msg <;> try rfl
  rename_i lr
  simp only
  cases hq : query m s (.inner k (law.call s i)) with
  | none => simp
  | some o =>
    simp only [Option.elim_some]
    cases hi : runIPA m child o.after (o.reachable hs) o.packet (child_statement st lr
      (law.call s i)) v <;> simp

/-- Total local rate at a chronological cut; failed transitions have no child access. -/
def treeLocalAtCut (m : AdversaryModel q A Ω S) : {d : ℕ} → {p : TreePlan q S d} →
    (cut : TreeCut p) → (s : Snapshot q S) → ReachableSnapshot m s → Packet q A →
    Statement q A d → cut.Prefix → ℚ
  | _, _, .here p, s, hs, msg, st, _ => treePathRate p m s hs msg st
  | d+1, _, .next law _ child cut, s, hs, msg, st, u => match msg with
    | .round lr => (query m s (.inner d (law.call s u.1))).elim 0 (fun o =>
        treeLocalAtCut m cut o.after (o.reachable hs) o.packet
          (child_statement st lr (law.call s u.1)) u.2)
    | _ => 0

set_option backward.isDefEq.respectTransparency false in
theorem tree_continuation_rate_eq_local (p : TreePlan q S k) (cut : TreeCut p)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (msg : Packet q A) (st : Statement q A k) (u : cut.Prefix) :
    eventRate (fun v : cut.Suffix => treePathEvent p m s hs msg st (cut.split.symm (u,v))) =
      treeLocalAtCut m cut s hs msg st u := by
  induction cut generalizing s msg with
  | here p => cases u; rfl
  | @next d law T child cut ih =>
    change eventRate (fun v => treePathEvent (.node law T child) m s hs msg st
      (u.1,cut.split.symm (u.2,v))) = _
    simp only [tree_path_event_node,treeLocalAtCut]
    cases hp : msg <;> try { simp }
    rename_i lr
    cases hq : query m s (.inner d (law.call s u.1)) with
    | none => simp
    | some o => exact ih o.after (o.reachable hs) o.packet _ u.2

theorem eta_cut_rate_local (p : EtaPlan q S k) (cut : TreeCut p.tree)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A)
    (e t : ZMod q) (j : Fin p.law.size) (u : cut.Prefix) :
    eventRate (fun v : cut.Suffix => etaPathEvent p claim m s hs ann e t
      (j,cut.split.symm (u,v))) =
      (query m s (.binding (p.law.call s j))).elim 0 (fun b =>
        treeLocalAtCut m cut b.after (b.reachable hs) b.packet
          (P.toIPA (C.responseClaim claim ann e t) (p.law.call s j)) u) := by
  simp only [etaPathEvent]
  cases hb : query m s (.binding (p.law.call s j)) with
  | none => exact eventRate_false
  | some b =>
    exact tree_continuation_rate_eq_local p.tree cut m b.after (b.reachable hs) b.packet _ u

set_option backward.isDefEq.respectTransparency false in
/-- Every canonical post-eta/round cut preserves the scalar prefix guard. -/
theorem continuation_round_eq_local (p : ProtocolPlan q S k) (cut : TreeCut p.eta.tree)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (c : Observation m (initialSnapshot m) .commit) (ann : F.Announcement A)
    (hc : query m (initialSnapshot m) .commit = some c) (ha : c.packet = .announcement ann)
    (i : Fin p.law.size) (j : Fin p.eta.law.size) (u : cut.Prefix) :
    continuationRate p claim m (afterRoundSplit p cut) ((i,j),u) =
      (query m c.after (.outer (p.law.call c.after i))).elim 0 (fun o => match o.packet with
        | .scalar t z => if C.scalarCheck claim ann (p.law.call c.after i) t z then
            (query m o.after (.binding (p.eta.law.call o.after j))).elim 0 (fun b =>
              treeLocalAtCut m cut b.after (b.reachable (o.reachable (c.reachable .initial)))
                b.packet
                (P.toIPA (C.responseClaim claim ann (p.law.call c.after i) t) (p.eta.law.call
                  o.after j)) u)
            else 0
        | _ => 0) := by
  have he : continuationRate p claim m (afterRoundSplit p cut) ((i,j),u) =
      eventRate (fun v : cut.Suffix => (execute p claim m (i,j,cut.split.symm (u,v))).any
        (fun r => r.accepted)) := by
    simp [continuationRate,afterRoundSplit,eventRate,AcceptedRun,Option.any_eq_true]
  rw [he]
  simp only [execute_event,hc,Option.elim_some,ha,outerPathEvent]
  cases hq : query m c.after (.outer (p.law.call c.after i)) with
  | none => simp
  | some o =>
    simp only [Option.elim_some]
    cases o.packet <;> try { exact eventRate_false }
    rename_i t z
    dsimp only
    by_cases hv : C.scalarCheck claim ann (p.law.call c.after i) t z
    · simp only [hv,decide_true,Bool.true_and,if_true]
      exact eta_cut_rate_local p.eta cut claim m o.after (o.reachable (c.reachable .initial))
        ann _ t j u
    · simp only [hv,decide_false,Bool.false_and,if_false]; exact eventRate_false

structure CryptoHiddenScalarThresholdQuotaContractSuite : Prop where
  profile_monotonicity : ∀ n T j (p p' : ℕ → ℚ), (∀ i < n, 0 ≤ p i) →
    (∀ i < n, p i ≤ p' i) → (∀ i < n, p' i ≤ 1) → quotaLower n p T j ≤ quotaLower n p' T j
  threshold_transfer : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S : Type) (k : ℕ) (p : ProtocolPlan q S k)
    (h : ThresholdProfile) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S),
    h.value 0 ≤ acceptanceRate p claim m → protocolThresholdBound p h ≤ p.bound claim m
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S : Type) (k : ℕ) (p : ProtocolPlan q S k)
    (h : ThresholdProfile) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S),
    h.value 0 ≤ acceptanceRate p claim m → 0 < protocolThresholdBound p h →
    ∃ w : p.Seed, ∃ f, (acquireCompressedFork claim m (p.decode m w)).outcome = .ok f ∧
      ForkProvenance m f ∧ F.ResultValid claim (C.extractCompressed claim f)

theorem verification_suite : CryptoHiddenScalarThresholdQuotaContractSuite where
  profile_monotonicity := quota_profile_mono
  threshold_transfer := fun _ _ _ _ _ _ _ _ _ => acceptance_threshold_le
  extraction := fun _ _ _ _ _ _ _ _ _ => threshold_positive_extracts

end CryptoHiddenScalarThresholdQuotaContract
