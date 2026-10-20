/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaProductContract

/-! Deficit bounds for the existing quota recursion. Blocks partition the budget
analytically; neither restarts nor independence of blocks are assumed. Exact child
threshold bounds and original plan laws are retained in the tape adapters. -/
namespace CryptoHiddenScalarQuotaDeficitContract
set_option backward.isDefEq.respectTransparency false
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarTapeAverageContract
open CryptoHiddenScalarHeavyTapeContract
open CryptoHiddenScalarQuotaMarginContract
open CryptoHiddenScalarQuotaProductContract

def quotaDeficit (n : ℕ) (p : ℕ → ℚ) (T j : ℕ) : ℚ :=
  1 - quotaLower n p T j

theorem quota_deficit_full (n T j : ℕ) (p : ℕ → ℚ) (hj : n ≤ j) :
    quotaDeficit n p T j = 0 := by simp [quotaDeficit, quota_full, hj]

theorem quota_deficit_range (n T j : ℕ) (p : ℕ → ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) :
    0 ≤ quotaDeficit n p T j ∧ quotaDeficit n p T j ≤ 1 := by
  have := quota_bounds n p hp T j
  dsimp [quotaDeficit]
  constructor <;> linarith

theorem quota_deficit_succ (n T j : ℕ) (p : ℕ → ℚ) (hj : j < n) :
    quotaDeficit n p (T + 1) j =
      (1 - p j) * quotaDeficit n p T j + p j * quotaDeficit n p T (j + 1) := by
  simp only [quotaDeficit, quotaLower, if_neg (by omega : ¬n ≤ j)]
  ring

theorem quota_deficit_step_antitone (n T j : ℕ) (p : ℕ → ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) :
    quotaDeficit n p T (j + 1) ≤ quotaDeficit n p T j := by
  exact sub_le_sub_left (quota_step_mono n p hp T j) 1

theorem quota_deficit_budget_antitone (n T T' j : ℕ) (p : ℕ → ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hT : T ≤ T') :
    quotaDeficit n p T' j ≤ quotaDeficit n p T j :=
  sub_le_sub_left (quota_budget_mono n T T' j p hp hT) 1

/-- Accumulated successes are retained between the two analytical blocks. -/
theorem quota_deficit_submultiplicative (n T L j : ℕ) (p : ℕ → ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) :
    quotaDeficit n p (T + L) j ≤ quotaDeficit n p T j * quotaDeficit n p L j := by
  induction T generalizing j with
  | zero =>
    by_cases hj : n ≤ j
    · simp [quota_deficit_full, hj]
    · simp [quotaDeficit, quotaLower, hj]
  | succ T ih =>
    by_cases hj : n ≤ j
    · simp [quota_deficit_full, hj]
    have hlt : j < n := by omega
    rw [show T + 1 + L = T + L + 1 by omega, quota_deficit_succ n (T + L) j p hlt,
      quota_deficit_succ n T j p hlt]
    have ha := mul_le_mul_of_nonneg_left (ih j) (sub_nonneg.mpr (hp j hlt).2)
    have hb := mul_le_mul_of_nonneg_left (ih (j + 1)) (hp j hlt).1
    have hc := mul_le_mul_of_nonneg_left (quota_deficit_step_antitone n L j p hp)
      (mul_nonneg (hp j hlt).1 (quota_deficit_range n T (j + 1) p hp).1)
    nlinarith

theorem quota_deficit_block_upper (n T L K j : ℕ) (p : ℕ → ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hT : K * L ≤ T) :
    quotaDeficit n p T j ≤ quotaDeficit n p L j ^ K := by
  have hh : quotaDeficit n p (K * L) j ≤ quotaDeficit n p L j ^ K := by
    clear hT
    induction K with
    | zero => simpa using (quota_deficit_range n 0 j p hp).2
    | succ K ih =>
      rw [Nat.succ_mul, pow_succ]
      exact (quota_deficit_submultiplicative n (K * L) L j p hp).trans
        (mul_le_mul_of_nonneg_right ih (quota_deficit_range n L j p hp).1)
  exact (quota_deficit_budget_antitone n (K * L) T j p hp hT).trans hh

theorem quota_deficit_product_upper (n T K j : ℕ) (p : ℕ → ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hj : j < n) (hT : K * (n - j) ≤ T) :
    quotaDeficit n p T j ≤ (1 - ∏ i ∈ Finset.Ico j n, p i) ^ K := by
  have hh := quota_deficit_block_upper n T (n - j) K j p hp hT
  simpa only [quotaDeficit, quota_diagonal n j p hj.le] using hh

theorem quota_deficit_product_floor (n T j : ℕ) (p : ℕ → ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hj : j < n) :
    quotaDeficit n p T j ≤ (1 - ∏ i ∈ Finset.Ico j n, p i) ^ (T / (n - j)) :=
  quota_deficit_product_upper n T _ j p hp hj (Nat.div_mul_le_self _ _)

theorem quota_deficit_uniform_upper (n T K j : ℕ) (p : ℕ → ℚ) (mu : ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hj : j < n) (hT : K * (n - j) ≤ T)
    (hm : 0 < mu) (_hm1 : mu ≤ 1) (hl : ∀ i ∈ Finset.Ico j n, mu ≤ p i) :
    quotaDeficit n p T j ≤ (1 - mu ^ (n - j)) ^ K := by
  have hprod : mu ^ (n - j) ≤ ∏ i ∈ Finset.Ico j n, p i := by
    simpa using Finset.prod_le_prod (s := Finset.Ico j n) (fun _ _ => hm.le) hl
  have hr : 0 ≤ 1 - ∏ i ∈ Finset.Ico j n, p i := by
    rw [← quota_diagonal n j p hj.le]
    exact (quota_deficit_range n (n - j) j p hp).1
  exact (quota_deficit_product_upper n T K j p hp hj hT).trans
    (pow_le_pow_left₀ hr (sub_le_sub_left hprod 1) _)

/-- Complement of the geometric deficit upper bound, including K = 0. -/
def blockLower (a : ℚ) (K : ℕ) : ℚ := 1 - (1 - a) ^ K

theorem block_lower_range (a : ℚ) (K : ℕ) (ha : 0 ≤ a ∧ a ≤ 1) :
    0 ≤ blockLower a K ∧ blockLower a K ≤ 1 := by
  have h0 := pow_nonneg (sub_nonneg.mpr ha.2) K
  have h1 : (1 - a) ^ K ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  dsimp [blockLower]
  constructor <;> linarith

theorem block_lower_mono (a b : ℚ) (K : ℕ) (hb : b ≤ 1) (hab : a ≤ b) :
    blockLower a K ≤ blockLower b K := by
  exact sub_le_sub_left (pow_le_pow_left₀ (sub_nonneg.mpr hb) (sub_le_sub_left hab 1) K) 1

theorem block_lower_positive (a : ℚ) (K : ℕ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hK : 1 ≤ K) : 0 < blockLower a K := by
  have hh : (1 - a) ^ K ≤ 1 - a := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right
      (pow_le_one₀ (by linarith : (0 : ℚ) ≤ 1 - a) (by linarith) : (1 - a) ^ t ≤ 1)
      (by linarith)).trans_eq (one_mul _)
  dsimp [blockLower]
  linarith

theorem linear_product_range (n : ℕ) (d beta : ℚ) (hd : d ≤ 1) (hb : 0 ≤ beta) :
    0 ≤ linearQuotaProduct n d beta ∧ linearQuotaProduct n d beta ≤ 1 := by
  refine ⟨linear_product_nonneg _ _ _, ?_⟩
  apply Finset.prod_le_one
  · intro i hi; exact le_max_left _ _
  · intro i hi
    exact max_le (by norm_num)
      ((sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hb)).trans hd)

theorem linear_block_lower (n T K : ℕ) (d beta : ℚ) (hn : 0 < n)
    (hd : d ≤ 1) (hb : 0 ≤ beta) (hT : K * n ≤ T) :
    blockLower (linearQuotaProduct n d beta) K ≤ quota n T d beta := by
  have hh := quota_deficit_product_upper n T K 0 (fun j => max 0 (d - (j : ℚ) * beta))
    (fun j _ => ⟨le_max_left _ _, max_le (by norm_num)
      ((sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hb)).trans hd)⟩) hn (by simpa using hT)
  simp only [← Finset.range_eq_Ico] at hh
  change 1 - quota n T d beta ≤ (1 - linearQuotaProduct n d beta) ^ K at hh
  dsimp [blockLower]
  linarith

theorem linear_uniform_deficit_upper (n T K : ℕ) (d beta mu : ℚ) (hn : 0 < n)
    (hd : d ≤ 1) (hb : 0 ≤ beta) (hT : K * n ≤ T) (hm : 0 < mu)
    (hmargin : mu ≤ d - ((n - 1 : ℕ) : ℚ) * beta) :
    1 - quota n T d beta ≤ (1 - mu ^ n) ^ K := by
  have hm1 : mu ≤ 1 := hmargin.trans
    ((sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hb)).trans hd)
  have hl : ∀ i ∈ Finset.Ico 0 n, mu ≤ max 0 (d - (i : ℚ) * beta) := by
    intro i hi
    have hi' : (i : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.le_sub_one_of_lt (Finset.mem_Ico.mp hi).2
    apply le_trans _ (le_max_right _ _)
    nlinarith [mul_le_mul_of_nonneg_right hi' hb]
  simpa only [Nat.sub_zero, quotaDeficit, quota] using quota_deficit_uniform_upper n T K 0
    (fun i => max 0 (d - (i : ℚ) * beta)) mu
    (fun i _ => ⟨le_max_left _ _, max_le (by norm_num)
      ((sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hb)).trans hd)⟩)
    hn (by simpa using hT) hm hm1 hl

theorem threshold_block_lower (h : ThresholdProfile) (n T K : ℕ) (beta b : ℚ)
    (hn : 0 < n) (hb : 0 ≤ beta) (hr : 0 ≤ b ∧ b ≤ 1) (hT : K * n ≤ T) :
    blockLower (linearQuotaProduct n (thresholdDensity h b) beta) K ≤
      thresholdStep h n T beta b :=
  linear_block_lower n T K _ beta hn (threshold_density_range h b hr).2 hb hT

variable {q k : ℕ} {A Ω S : Type}

theorem tree_node_block_lower (law : CallLaw (Snapshot q S) (ZMod q)ˣ (ZMod q)
    (fun x => (x : ZMod q) ^ 2)) (T K : ℕ) (child : TreePlan q S k)
    (h : ThresholdProfile) (hT : 4 * K ≤ T) :
    blockLower (linearQuotaProduct 4
      (thresholdDensity h (treeThresholdBound child h.tail)) law.beta) K ≤
      treeThresholdBound (.node law T child) h :=
  threshold_block_lower h 4 T K _ _ (by decide) law.beta_nonneg
    (tree_threshold_range child h.tail) (by omega)

theorem eta_block_lower (p : EtaPlan q S k) (h : ThresholdProfile) (K : ℕ)
    (hT : 2 * K ≤ p.budget) :
    blockLower (linearQuotaProduct 2
      (thresholdDensity h (treeThresholdBound p.tree h.tail)) p.law.beta) K ≤
      etaThresholdBound p h :=
  threshold_block_lower h 2 p.budget K _ _ (by decide) p.law.beta_nonneg
    (tree_threshold_range p.tree h.tail) (by omega)

theorem protocol_product_range (p : ProtocolPlan q S k) (h : ThresholdProfile) :
    0 ≤ protocolProductLower p h ∧ protocolProductLower p h ≤ 1 :=
  linear_product_range 3 _ _
    (threshold_density_range h _ (eta_threshold_range p.eta h.tail)).2 p.law.beta_nonneg

theorem protocol_block_lower (p : ProtocolPlan q S k) (h : ThresholdProfile) (K : ℕ)
    (hT : 3 * K ≤ p.budget) :
    blockLower (protocolProductLower p h) K ≤ protocolThresholdBound p h :=
  threshold_block_lower h 3 p.budget K _ _ (by decide) p.law.beta_nonneg
    (eta_threshold_range p.eta h.tail) (by omega)

theorem finiteProductLower_range (E : TapeExperiment q A Ω S k) (G : Finset Ω) :
    0 ≤ finiteProductLower E G ∧ finiteProductLower E G ≤ 1 := by
  by_cases hg : G.Nonempty
  · have hm := Finset.min'_mem (G.image (fun w => protocolProductLower (E.plan w)
      (E.thresholds w))) (hg.image _)
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hm
    rw [finiteProductLower, dif_pos hg, ← he]
    exact protocol_product_range _ _
  · simp [finiteProductLower, hg]

section Weighted
variable [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A]
  [Fintype Ω] [DecidableEq Ω]

theorem block_average_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (K : ℕ)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget) :
    blockLower (finiteProductLower E G) K * TapeLaw.mass W G ≤ E.averagedBound W claim := by
  apply TapeExperiment.averaged_lower_on_good E W claim G hg
  intro w hw
  exact (block_lower_mono _ _ K (protocol_product_range (E.plan w) (E.thresholds w)).2
    (finiteProductLower_le E G w hw)).trans (protocol_block_lower _ _ K (hT w hw))

theorem block_success_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (K : ℕ)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget) :
    blockLower (finiteProductLower E G) K * TapeLaw.mass W G ≤ E.successProbability W claim :=
  (block_average_lower E W claim G K hg hT).trans (E.averaged_acquisition_lower W claim)

/-- The unqualified mass is retained; no convergence to global success 1 is asserted. -/
theorem block_failure_upper (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (K : ℕ)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget) :
    1 - E.successProbability W claim ≤ 1 - TapeLaw.mass W G +
      TapeLaw.mass W G * (1 - finiteProductLower E G) ^ K := by
  have hh := block_success_lower E W claim G K hg hT
  dsimp [blockLower] at hh
  nlinarith

/-- Certificates imply budget 3, not budget 3K. The latter remains an explicit premise. -/
theorem certified_block_success_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (K : ℕ) (hK : 1 ≤ K)
    (hg : G ⊆ TapeExperiment.qualifying E claim) (hm : 0 < TapeLaw.mass W G)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget)
    (hc : ∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) :
    0 < blockLower (finiteProductLower E G) K * TapeLaw.mass W G ∧
    blockLower (finiteProductLower E G) K * TapeLaw.mass W G ≤ E.averagedBound W claim ∧
    E.averagedBound W claim ≤ E.successProbability W claim :=
  ⟨mul_pos (block_lower_positive _ K
    (finiteProductLower_positive E G (nonempty_of_mass_pos W G hm) hc)
    (finiteProductLower_range E G).2 hK) hm,
    block_average_lower E W claim G K hg hT, E.averaged_acquisition_lower W claim⟩

theorem block_extracts (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (K : ℕ) (hK : 1 ≤ K)
    (hg : G ⊆ TapeExperiment.qualifying E claim) (hm : 0 < TapeLaw.mass W G)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget)
    (hc : ∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) :
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧
        F.ResultValid claim (C.extractCompressed claim f) := by
  have hh := certified_block_success_lower E W claim G K hK hg hm hT hc
  exact E.positive_mass_extracts W claim (hh.1.trans_le hh.2.1)
end Weighted

structure CryptoHiddenScalarQuotaDeficitContractSuite : Prop where
  submultiplicative : ∀ (n T L j : ℕ) (p : ℕ → ℚ),
    (∀ i < n, 0 ≤ p i ∧ p i ≤ 1) →
    quotaDeficit n p (T + L) j ≤ quotaDeficit n p T j * quotaDeficit n p L j
  blocks : ∀ (n T L K j : ℕ) (p : ℕ → ℚ),
    (∀ i < n, 0 ≤ p i ∧ p i ≤ 1) → K * L ≤ T →
    quotaDeficit n p T j ≤ quotaDeficit n p L j ^ K
  protocol : ∀ (q k : ℕ) (S : Type) (p : ProtocolPlan q S k) (h : ThresholdProfile) (K : ℕ),
    3 * K ≤ p.budget → blockLower (protocolProductLower p h) K ≤ protocolThresholdBound p h

theorem verification_suite : CryptoHiddenScalarQuotaDeficitContractSuite where
  submultiplicative := quota_deficit_submultiplicative
  blocks := quota_deficit_block_upper
  protocol := by intros; apply protocol_block_lower; assumption
end CryptoHiddenScalarQuotaDeficitContract
