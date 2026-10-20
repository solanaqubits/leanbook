/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaDeficitContract

/-! Constructive minimal block counts for a geometric deficit majorant.
Minimality is not minimality of the actual acquisition budget. Original exact
child bounds, microseed laws, qualification and explicit budgets are retained. -/
namespace CryptoHiddenScalarQuotaBudgetContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaProductContract
open CryptoHiddenScalarQuotaMarginContract
open CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarTapeAverageContract
open CryptoHiddenScalarHeavyTapeContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract

/-- A bounded, executable search; the first successful index is retained. -/
def searchThrough (p : ℕ → Prop) [DecidablePred p] : ℕ → Option ℕ
  | 0 => if p 0 then some 0 else none
  | N + 1 => match searchThrough p N with
    | some k => some k
    | none => if p (N + 1) then some (N + 1) else none

theorem searchThrough_spec (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    match searchThrough p N with
    | some k => k ≤ N ∧ p k ∧ ∀ i < k, ¬ p i
    | none => ∀ i ≤ N, ¬ p i := by
  induction N with
  | zero => by_cases h : p 0 <;> simp [searchThrough, h]
  | succ N ih =>
    cases hs : searchThrough p N with
    | some k =>
      rw [hs] at ih
      simp only [searchThrough, hs]
      exact ⟨Nat.le_succ_of_le ih.1, ih.2⟩
    | none =>
      rw [hs] at ih
      by_cases h : p (N + 1)
      · simp only [searchThrough, hs, if_pos h]
        exact ⟨le_rfl, h, fun i hi => ih i (by omega)⟩
      · simp only [searchThrough, hs, if_neg h]
        intro i hi
        by_cases he : i = N + 1
        · simpa [he] using h
        · exact ih i (by omega)

theorem searchThrough_some (p : ℕ → Prop) [DecidablePred p] (N K : ℕ)
    (h : searchThrough p N = some K) : K ≤ N ∧ p K ∧ ∀ i < K, ¬ p i := by
  simpa only [h] using searchThrough_spec p N

theorem searchThrough_none (p : ℕ → Prop) [DecidablePred p] (N : ℕ)
    (h : searchThrough p N = none) : ∀ i ≤ N, ¬ p i := by
  simpa only [h] using searchThrough_spec p N

/-- Elementary rational bound, avoiding real logarithms and floating rounding. -/
theorem geometric_reciprocal_upper (P : ℚ) (hP : 0 ≤ P) (hP1 : P ≤ 1) (K : ℕ) :
    (1 - P)^K ≤ 1 / (1 + (K : ℚ) * P) := by
  have hd : 0 < 1 + (K : ℚ) * P := by positivity
  apply (le_div_iff₀ hd).mpr
  clear hd
  induction K with
  | zero => simp
  | succ K ih =>
    have hz : 0 ≤ (1 - P)^K := pow_nonneg (sub_nonneg.mpr hP1) _
    have hh : (1 - P)^K * ((K : ℚ) + 1) * P ^ 2 ≥ 0 := by positivity
    rw [pow_succ, Nat.cast_succ]
    nlinarith

def geometricBudgetCap (P ε : ℚ) : ℕ := ⌈(1 - ε)/(P * ε)⌉₊

theorem geometricBudgetCap_sufficient (P ε : ℚ) (hP : 0 < P) (hP1 : P ≤ 1)
    (hε : 0 < ε) (_hε1 : ε < 1) : (1 - P)^geometricBudgetCap P ε ≤ ε := by
  have hc : (1 - ε)/(P * ε) ≤ (geometricBudgetCap P ε : ℚ) := Nat.le_ceil _
  have hm : 1 - ε ≤ (geometricBudgetCap P ε : ℚ) * (P * ε) :=
    (div_le_iff₀ (mul_pos hP hε)).mp hc
  apply (geometric_reciprocal_upper P hP.le hP1 _).trans
  apply (div_le_iff₀ (by positivity : 0 < 1 + (geometricBudgetCap P ε : ℚ) * P)).mpr
  nlinarith

/-- Invalid inputs and unattainable valid targets both return none. Impossibility
interpretations require explicit admissibility. Zero tolerance is supported. -/
def chooseBlockCount (P ε : ℚ) : Option ℕ :=
  if ¬ (0 ≤ P ∧ P ≤ 1 ∧ 0 ≤ ε) then none
  else if 1 ≤ ε then some 0
  else if P = 1 then some 1
  else if P = 0 ∨ ε = 0 then none
  else searchThrough (fun k => (1 - P)^k ≤ ε) (geometricBudgetCap P ε)

theorem chooseBlockCount_spec (P ε : ℚ) (K : ℕ)
    (h : chooseBlockCount P ε = some K) :
    (0 ≤ P ∧ P ≤ 1 ∧ 0 ≤ ε) ∧ (1 - P)^K ≤ ε ∧ ∀ i < K, ε < (1 - P)^i := by
  unfold chooseBlockCount at h
  split_ifs at h with hv he hp hz
  · have hk : K = 0 := (Option.some.inj h).symm
    subst K
    exact ⟨hv, by simpa using he, by simp⟩
  · have hk : K = 1 := (Option.some.inj h).symm
    subst K
    refine ⟨hv, by simpa [hp] using hv.2.2, ?_⟩
    intro i hi
    have : i = 0 := by omega
    simpa [this] using lt_of_not_ge he
  · have hh := searchThrough_some _ _ K h
    exact ⟨hv, hh.2.1, fun i hi => lt_of_not_ge (hh.2.2 i hi)⟩

theorem chooseBlockCount_sound (P ε : ℚ) (K : ℕ)
    (h : chooseBlockCount P ε = some K) : (1 - P)^K ≤ ε :=
  (chooseBlockCount_spec P ε K h).2.1

theorem chooseBlockCount_minimal (P ε : ℚ) (K : ℕ)
    (h : chooseBlockCount P ε = some K) : ∀ i < K, ε < (1 - P)^i :=
  (chooseBlockCount_spec P ε K h).2.2

theorem chooseBlockCount_positive (P ε : ℚ) (K : ℕ)
    (h : chooseBlockCount P ε = some K) (he : ε < 1) : 0 < K := by
  have hs := chooseBlockCount_sound P ε K h
  by_contra hn
  have : K = 0 := by omega
  simp only [this, pow_zero] at hs
  linarith

theorem chooseBlockCount_exists (P ε : ℚ) (hP : 0 < P) (hP1 : P ≤ 1)
    (hε : 0 < ε) : ∃ K, chooseBlockCount P ε = some K := by
  unfold chooseBlockCount
  rw [if_neg (not_not.mpr ⟨hP.le,hP1,hε.le⟩)]
  split_ifs with he hp hz
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · rcases hz with hz | hz <;> linarith
  · cases hs : searchThrough (fun k => (1 - P)^k ≤ ε) (geometricBudgetCap P ε) with
    | some K => exact ⟨K,rfl⟩
    | none =>
      exact False.elim (searchThrough_none _ _ hs _ le_rfl
        (geometricBudgetCap_sufficient P ε hP hP1 hε (lt_of_not_ge he)))

theorem chooseBlockCount_one (ε : ℚ) (he : 0 ≤ ε) (he1 : ε < 1) :
    chooseBlockCount 1 ε = some 1 := by simp [chooseBlockCount, he, not_le.mpr he1]

theorem chooseBlockCount_large_tolerance (P ε : ℚ) (hP : 0 ≤ P) (hP1 : P ≤ 1)
    (he : 1 ≤ ε) : chooseBlockCount P ε = some 0 := by
  simp [chooseBlockCount, hP, hP1, le_trans (by norm_num : (0 : ℚ) ≤ 1) he, he]

theorem chooseBlockCount_none_iff (P ε : ℚ) (hP : 0 ≤ P) (hP1 : P ≤ 1) (he : 0 ≤ ε) :
    chooseBlockCount P ε = none ↔ ∀ K, ε < (1 - P)^K := by
  constructor
  · intro hn
    by_cases h1 : 1 ≤ ε
    · rw [chooseBlockCount_large_tolerance P ε hP hP1 h1] at hn; contradiction
    by_cases hp : P = 1
    · subst P; rw [chooseBlockCount_one ε he (lt_of_not_ge h1)] at hn; contradiction
    by_cases hz : P = 0
    · simp [hz, lt_of_not_ge h1]
    have hpos : 0 < P := lt_of_le_of_ne hP (Ne.symm hz)
    by_cases hez : ε = 0
    · subst ε
      exact fun K => pow_pos (sub_pos.mpr (lt_of_le_of_ne hP1 hp)) K
    obtain ⟨K,hK⟩ := chooseBlockCount_exists P ε hpos hP1 (lt_of_le_of_ne he (Ne.symm hez))
    rw [hn] at hK; contradiction
  · intro hall
    cases h : chooseBlockCount P ε with
    | none => rfl
    | some K => exact False.elim (not_lt_of_ge (chooseBlockCount_sound P ε K h) (hall K))

theorem chooseBlockCount_invalid (P ε : ℚ) (h : ¬ (0 ≤ P ∧ P ≤ 1 ∧ 0 ≤ ε)) :
    chooseBlockCount P ε = none := by simp [chooseBlockCount, h]

theorem chooseBlockCount_zero (ε : ℚ) (he : 0 ≤ ε) (he1 : ε < 1) :
    chooseBlockCount 0 ε = none := by simp [chooseBlockCount, he, not_le.mpr he1]

theorem chooseBlockCount_zero_tolerance (P : ℚ) (hP : 0 ≤ P) (hP1 : P < 1) :
    chooseBlockCount P 0 = none := by simp [chooseBlockCount, hP, hP1.le, ne_of_lt hP1]

theorem selected_quota_deficit_le (n T j K : ℕ) (p : ℕ → ℚ) (ε : ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hj : j < n)
    (hK : chooseBlockCount (∏ i ∈ Finset.Ico j n, p i) ε = some K)
    (hT : K * (n - j) ≤ T) : quotaDeficit n p T j ≤ ε :=
  (quota_deficit_product_upper n T K j p hp hj hT).trans
    (chooseBlockCount_sound _ _ _ hK)

theorem absorbed_quota_deficit_le (n T j : ℕ) (p : ℕ → ℚ) (ε : ℚ)
    (hj : n ≤ j) (he : 0 ≤ ε) : quotaDeficit n p T j ≤ ε := by
  simpa only [quota_deficit_full n T j p hj] using he

theorem selected_block_lower (P ε : ℚ) (K : ℕ)
    (hK : chooseBlockCount P ε = some K) : 1 - ε ≤ blockLower P K :=
  sub_le_sub_left (chooseBlockCount_sound _ _ _ hK) 1

variable {q k : ℕ} {A Ω S : Type}

/-- Root completion deficit only; child tolerances are not replaced. -/
theorem selected_root_deficit_le (E : TapeExperiment q A Ω S k) (G : Finset Ω)
    (ε : ℚ) (K : ℕ) (hK : chooseBlockCount (finiteProductLower E G) ε = some K)
    (w : Ω) (hw : w ∈ G) (hT : 3 * K ≤ (E.plan w).budget) :
    1 - protocolThresholdBound (E.plan w) (E.thresholds w) ≤ ε := by
  have hl := selected_block_lower _ _ _ hK
  have hm := block_lower_mono _ _ K (protocol_product_range (E.plan w) (E.thresholds w)).2
    (finiteProductLower_le E G w hw)
  have hb := protocol_block_lower (E.plan w) (E.thresholds w) K hT
  linarith

section Weighted
variable [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A]
  [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
/-- On a qualified tape the root bound transfers to actual acquisition. -/
theorem selected_tape_failure_le (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k)
    (G : Finset Ω) (ε : ℚ) (K : ℕ)
    (hK : chooseBlockCount (finiteProductLower E G) ε = some K)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (w : Ω) (hw : w ∈ G) (hT : 3 * K ≤ (E.plan w).budget) :
    1 - eventRate (E.success claim w) ≤ ε := by
  have hb := selected_root_deficit_le E G ε K hK w hw hT
  have hq : E.qualifies claim w := (Finset.mem_filter.mp (hg hw)).2
  have ha := E.guarded_acquisition_lower claim w
  rw [TapeExperiment.guardedBound, if_pos hq] at ha
  linarith

theorem selected_average_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (ε : ℚ) (K : ℕ)
    (hK : chooseBlockCount (finiteProductLower E G) ε = some K)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget) :
    (1 - ε) * TapeLaw.mass W G ≤ E.averagedBound W claim :=
  (mul_le_mul_of_nonneg_right (selected_block_lower _ _ _ hK) (TapeLaw.mass_nonneg W G)).trans
    (block_average_lower E W claim G K hg hT)

theorem selected_success_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (ε : ℚ) (K : ℕ)
    (hK : chooseBlockCount (finiteProductLower E G) ε = some K)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget) :
    (1 - ε) * TapeLaw.mass W G ≤ E.successProbability W claim :=
  (selected_average_lower E W claim G ε K hK hg hT).trans (E.averaged_acquisition_lower W claim)

/-- The mass outside G remains even when the conditional tolerance is small. -/
theorem selected_failure_upper (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (ε : ℚ) (K : ℕ)
    (hK : chooseBlockCount (finiteProductLower E G) ε = some K)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget) :
    1 - E.successProbability W claim ≤ 1 - TapeLaw.mass W G + TapeLaw.mass W G * ε := by
  have := selected_success_lower E W claim G ε K hK hg hT
  nlinarith

theorem selected_positive_average (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (ε : ℚ) (K : ℕ)
    (hK : chooseBlockCount (finiteProductLower E G) ε = some K)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget)
    (hm : 0 < TapeLaw.mass W G) (he : ε < 1) :
    0 < (1 - ε) * TapeLaw.mass W G ∧ (1 - ε) * TapeLaw.mass W G ≤ E.averagedBound W claim :=
  ⟨mul_pos (sub_pos.mpr he) hm, selected_average_lower E W claim G ε K hK hg hT⟩

theorem selected_extracts (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (ε : ℚ) (K : ℕ)
    (hK : chooseBlockCount (finiteProductLower E G) ε = some K)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hT : ∀ w ∈ G, 3 * K ≤ (E.plan w).budget)
    (hm : 0 < TapeLaw.mass W G) (he : ε < 1) :
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w)
        ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧
        F.ResultValid claim (C.extractCompressed claim f) := by
  have hh := selected_positive_average E W claim G ε K hK hg hT hm he
  exact E.positive_mass_extracts W claim (hh.1.trans_le hh.2)
end Weighted

structure CryptoHiddenScalarQuotaBudgetContractSuite : Prop where
  selector_sound : ∀ (P ε : ℚ) (K : ℕ), chooseBlockCount P ε = some K → (1 - P)^K ≤ ε
  selector_minimal : ∀ (P ε : ℚ) (K : ℕ), chooseBlockCount P ε = some K →
    ∀ i < K, ε < (1 - P)^i
  selector_exists : ∀ (P ε : ℚ), 0 < P → P ≤ 1 → 0 < ε →
    ∃ K, chooseBlockCount P ε = some K
  quota : ∀ (n T j K : ℕ) (p : ℕ → ℚ) (ε : ℚ),
    (∀ i < n, 0 ≤ p i ∧ p i ≤ 1) → j < n →
    chooseBlockCount (∏ i ∈ Finset.Ico j n, p i) ε = some K → K * (n - j) ≤ T →
    quotaDeficit n p T j ≤ ε

theorem verification_suite : CryptoHiddenScalarQuotaBudgetContractSuite where
  selector_sound := chooseBlockCount_sound
  selector_minimal := chooseBlockCount_minimal
  selector_exists := chooseBlockCount_exists
  quota := selected_quota_deficit_le
end CryptoHiddenScalarQuotaBudgetContract
