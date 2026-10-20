/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaMarginContract

/-! Explicit factorized bounds for the existing quota recursion. Algebraic diagonal
identities need no probability ranges; budget comparisons do. Plan adapters retain
the exact child threshold bound. Tape comparisons require sufficient root budgets. -/
namespace CryptoHiddenScalarQuotaProductContract
set_option backward.isDefEq.respectTransparency false
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarTapeAverageContract
open CryptoHiddenScalarHeavyTapeContract
open CryptoHiddenScalarQuotaMarginContract

theorem quota_insufficient (n T j : ℕ) (p : ℕ → ℚ) (h : j + T < n) :
    quotaLower n p T j = 0 :=
  CryptoHiddenScalarForkProgressProbabilityContract.quota_insufficient n p T j (by omega)

/-- Exact diagonal, even for profiles outside the probability interval. -/
theorem quota_diagonal (n j : ℕ) (p : ℕ → ℚ) (hj : j ≤ n) :
    quotaLower n p (n - j) j = ∏ i ∈ Finset.Ico j n, p i := by
  generalize he : n - j = T
  induction T generalizing j with
  | zero =>
    have : j = n := by omega
    subst j
    simp
  | succ T ih =>
    have hlt : j < n := by omega
    rw [quotaLower, if_neg (by omega), quota_insufficient n T j p (by omega)]
    rw [ih (j + 1) (by omega) (by omega)]
    simpa using (Finset.prod_eq_prod_Ico_succ_bot hlt p).symm

theorem quota_budget_mono (n T T' j : ℕ) (p : ℕ → ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hT : T ≤ T') :
    quotaLower n p T j ≤ quotaLower n p T' j := by
  apply (monotone_nat_of_le_succ (f := fun t => quotaLower n p t j) ?_) hT
  intro t
  by_cases h : n ≤ j
  · simp [quota_full, h]
  rw [quotaLower, if_neg h]
  have hm := quota_step_mono n p hp t j
  have h0 := (hp j (by omega)).1
  nlinarith

theorem quota_product_lower (n T j : ℕ) (p : ℕ → ℚ) (hj : j ≤ n)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hT : n - j ≤ T) :
    (∏ i ∈ Finset.Ico j n, p i) ≤ quotaLower n p T j := by
  rw [← quota_diagonal n j p hj]
  exact quota_budget_mono n (n - j) T j p hp hT

def linearQuotaProduct (n : ℕ) (d beta : ℚ) : ℚ :=
  ∏ j ∈ Finset.range n, max 0 (d - (j : ℚ) * beta)

theorem linear_product_nonneg (n : ℕ) (d beta : ℚ) :
    0 ≤ linearQuotaProduct n d beta :=
  Finset.prod_nonneg (fun _ _ => le_max_left _ _)

theorem linear_product_lower (n T : ℕ) (d beta : ℚ)
    (_hd : 0 ≤ d) (hd1 : d ≤ 1) (hb : 0 ≤ beta) (hT : n ≤ T) :
    linearQuotaProduct n d beta ≤ quota n T d beta := by
  change (∏ j ∈ Finset.range n, max 0 (d - (j : ℚ) * beta)) ≤ quotaLower n _ T 0
  simpa only [Nat.sub_zero, Finset.range_eq_Ico] using
    quota_product_lower n T 0 (fun j => max 0 (d - (j : ℚ) * beta)) (by omega)
      (fun j _ => ⟨le_max_left _ _, max_le (by norm_num)
        ((sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hb)).trans hd1)⟩) (by omega)

theorem linear_product_eq_of_margin (n : ℕ) (d beta : ℚ) (_hn : 0 < n)
    (hb : 0 ≤ beta) (hm : ((n - 1 : ℕ) : ℚ) * beta < d) :
    linearQuotaProduct n d beta = ∏ j ∈ Finset.range n, (d - (j : ℚ) * beta) := by
  apply Finset.prod_congr rfl
  intro j hj
  have hjn : (j : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
  rw [max_eq_right]
  nlinarith [mul_le_mul_of_nonneg_right hjn hb]

theorem uniform_margin_power_lower (n T : ℕ) (d beta mu : ℚ)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hb : 0 ≤ beta) (hT : n ≤ T)
    (hmu : 0 < mu) (hm : mu ≤ d - ((n - 1 : ℕ) : ℚ) * beta) :
    0 < mu ^ n ∧ mu ^ n ≤ linearQuotaProduct n d beta ∧
      linearQuotaProduct n d beta ≤ quota n T d beta := by
  refine ⟨pow_pos hmu _, ?_, linear_product_lower n T d beta hd hd1 hb hT⟩
  have hh : (∏ _j ∈ Finset.range n, mu) ≤ linearQuotaProduct n d beta := by
    apply Finset.prod_le_prod (fun _ _ => hmu.le)
    intro j hj
    have hjn : (j : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
    apply le_trans _ (le_max_right _ _)
    nlinarith [mul_le_mul_of_nonneg_right hjn hb]
  simpa using hh

theorem linear_product_positive (n : ℕ) (d beta : ℚ)
    (hb : 0 ≤ beta) (hm : ((n - 1 : ℕ) : ℚ) * beta < d) :
    0 < linearQuotaProduct n d beta := by
  apply Finset.prod_pos
  intro j hj
  have hjn : (j : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
  apply lt_of_lt_of_le _ (le_max_right _ _)
  nlinarith [mul_le_mul_of_nonneg_right hjn hb]

/-- The child bound is the existing exact threshold bound, never a recursively
substituted product estimate. -/
theorem threshold_product_lower (h : ThresholdProfile) (n T : ℕ) (beta b : ℚ)
    (hb : 0 ≤ beta) (hr : 0 ≤ b ∧ b ≤ 1) (hT : n ≤ T) :
    linearQuotaProduct n (thresholdDensity h b) beta ≤ thresholdStep h n T beta b :=
  linear_product_lower n T _ beta (threshold_density_range h b hr).1
    (threshold_density_range h b hr).2 hb hT

variable {q k : ℕ} {A Ω S : Type}

theorem tree_node_product_lower (law : CallLaw (Snapshot q S) (ZMod q)ˣ (ZMod q)
    (fun x => (x : ZMod q) ^ 2)) (T : ℕ) (child : TreePlan q S k)
    (h : ThresholdProfile) (hT : 4 ≤ T) :
    linearQuotaProduct 4 (thresholdDensity h (treeThresholdBound child h.tail)) law.beta ≤
      treeThresholdBound (.node law T child) h :=
  threshold_product_lower h 4 T _ _ law.beta_nonneg (tree_threshold_range child h.tail) hT

theorem eta_product_lower (p : EtaPlan q S k) (h : ThresholdProfile) (hT : 2 ≤ p.budget) :
    linearQuotaProduct 2 (thresholdDensity h (treeThresholdBound p.tree h.tail)) p.law.beta ≤
      etaThresholdBound p h :=
  threshold_product_lower h 2 p.budget _ _ p.law.beta_nonneg (tree_threshold_range p.tree h.tail) hT

/-- Pure diagonal product: a root budget premise is deliberately not built in. -/
def protocolProductLower (p : ProtocolPlan q S k) (h : ThresholdProfile) : ℚ :=
  linearQuotaProduct 3 (thresholdDensity h (etaThresholdBound p.eta h.tail)) p.law.beta

theorem protocol_product_lower (p : ProtocolPlan q S k) (h : ThresholdProfile)
    (hT : 3 ≤ p.budget) : protocolProductLower p h ≤ protocolThresholdBound p h :=
  threshold_product_lower h 3 p.budget _ _ p.law.beta_nonneg (eta_threshold_range p.eta h.tail) hT

theorem protocol_product_positive (p : ProtocolPlan q S k) (h : ThresholdProfile)
    (hc : protocolMarginCertificate p h) : 0 < protocolProductLower p h :=
  linear_product_positive 3 _ p.law.beta p.law.beta_nonneg (by simpa using hc.2.2)

def finiteProductLower (E : TapeExperiment q A Ω S k) (G : Finset Ω) : ℚ :=
  if hg : G.Nonempty then
    (G.image (fun w => protocolProductLower (E.plan w) (E.thresholds w))).min' (hg.image _)
  else 0

@[simp] theorem finiteProductLower_empty (E : TapeExperiment q A Ω S k) :
    finiteProductLower E ∅ = 0 := by simp [finiteProductLower]

theorem finiteProductLower_le (E : TapeExperiment q A Ω S k) (G : Finset Ω)
    (w : Ω) (hw : w ∈ G) :
    finiteProductLower E G ≤ protocolProductLower (E.plan w) (E.thresholds w) := by
  rw [finiteProductLower, dif_pos ⟨w,hw⟩]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩)

theorem finiteProductLower_positive (E : TapeExperiment q A Ω S k) (G : Finset Ω)
    (hg : G.Nonempty)
    (hc : ∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) :
    0 < finiteProductLower E G := by
  rw [finiteProductLower, dif_pos hg, Finset.lt_min'_iff]
  intro y hy
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
  exact protocol_product_positive _ _ (hc w hw)

/-- Without the budget premise the inequality is false, even for a singleton. -/
theorem finiteProductLower_le_root (E : TapeExperiment q A Ω S k) (G : Finset Ω)
    (hT : ∀ w ∈ G, 3 ≤ (E.plan w).budget) :
    finiteProductLower E G ≤ finiteRootLower E G := by
  by_cases hg : G.Nonempty
  · have hm := Finset.min'_mem (G.image (fun w => protocolThresholdBound (E.plan w)
      (E.thresholds w))) (hg.image _)
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hm
    rw [finiteRootLower, dif_pos hg, ← he]
    exact (finiteProductLower_le E G w hw).trans (protocol_product_lower _ _ (hT w hw))
  · simp [finiteProductLower, finiteRootLower, hg]

section Weighted
variable [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A]
  [Fintype Ω] [DecidableEq Ω]

theorem product_average_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 ≤ (E.plan w).budget) :
    finiteProductLower E G * TapeLaw.mass W G ≤ E.averagedBound W claim :=
  (mul_le_mul_of_nonneg_right (finiteProductLower_le_root E G hT)
    (TapeLaw.mass_nonneg W G)).trans
    (certified_average_lower E W claim G hg)

theorem product_success_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 ≤ (E.plan w).budget) :
    finiteProductLower E G * TapeLaw.mass W G ≤ E.successProbability W claim :=
  (product_average_lower E W claim G hg hT).trans
    (E.averaged_acquisition_lower W claim)

theorem certified_product_success_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω)
    (hg : G ⊆ TapeExperiment.qualifying E claim) (hm : 0 < TapeLaw.mass W G)
    (hc : ∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) :
    0 < finiteProductLower E G * TapeLaw.mass W G ∧
    finiteProductLower E G * TapeLaw.mass W G ≤ E.averagedBound W claim ∧
    E.averagedBound W claim ≤ E.successProbability W claim :=
  ⟨mul_pos (finiteProductLower_positive E G (nonempty_of_mass_pos W G hm) hc) hm,
    product_average_lower E W claim G hg (fun w hw => (hc w hw).2.1),
    E.averaged_acquisition_lower W claim⟩

theorem product_extracts (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω)
    (hg : G ⊆ TapeExperiment.qualifying E claim) (hm : 0 < TapeLaw.mass W G)
    (hc : ∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) :
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧
        F.ResultValid claim (C.extractCompressed claim f) := by
  have h := certified_product_success_lower E W claim G hg hm hc
  exact E.positive_mass_extracts W claim (h.1.trans_le h.2.1)
end Weighted

structure CryptoHiddenScalarQuotaProductContractSuite : Prop where
  diagonal : ∀ (n j : ℕ) (p : ℕ → ℚ), j ≤ n →
    quotaLower n p (n - j) j = ∏ i ∈ Finset.Ico j n, p i
  budget : ∀ (n T T' j : ℕ) (p : ℕ → ℚ),
    (∀ i < n, 0 ≤ p i ∧ p i ≤ 1) → T ≤ T' → quotaLower n p T j ≤ quotaLower n p T' j
  minimum : ∀ (q k : ℕ) (A Ω S : Type) (E : TapeExperiment q A Ω S k) (G : Finset Ω),
    (∀ w ∈ G, 3 ≤ (E.plan w).budget) → finiteProductLower E G ≤ finiteRootLower E G

theorem verification_suite : CryptoHiddenScalarQuotaProductContractSuite where
  diagonal := quota_diagonal
  budget := quota_budget_mono
  minimum := by intros; apply finiteProductLower_le_root; assumption
end CryptoHiddenScalarQuotaProductContract
