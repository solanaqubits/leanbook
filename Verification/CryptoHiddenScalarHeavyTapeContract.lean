/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarTapeAverageContract

/-! Weighted heavy-tape bounds, including tape-dependent cutoffs. A lower bound on
qualifying mass is combined with positive quota bounds on good tapes, preserving
all original ProtocolPlan seed laws. No new collector or extractor is introduced. -/
namespace CryptoHiddenScalarHeavyTapeContract
set_option backward.isDefEq.respectTransparency false
open CryptoHiddenScalarTapeAverageContract
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarSinglePathContract
open CryptoHiddenScalarThresholdQuotaContract

namespace TapeLaw
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def mass (W : TapeLaw Ω) (G : Finset Ω) : ℚ :=
  W.expectation (fun w => if w ∈ G then 1 else 0)

theorem mass_nonneg (W : TapeLaw Ω) (G : Finset Ω) : 0 ≤ mass W G :=
  W.expectation_nonneg _ fun _ => by split_ifs <;> norm_num

theorem mass_mono (W : TapeLaw Ω) {G H : Finset Ω} (h : G ⊆ H) :
    mass W G ≤ mass W H := W.expectation_mono _ _ fun w => by
  by_cases hw : w ∈ G
  · simp [hw, h hw]
  · simp [hw]; split_ifs <;> norm_num

theorem mass_le_one (W : TapeLaw Ω) (G : Finset Ω) : mass W G ≤ 1 := by
  calc
    _ ≤ W.expectation (fun _ => 1) := W.expectation_mono _ _ fun _ => by
      split_ifs <;> norm_num
    _ = 1 := W.expectation_one

omit [DecidableEq Ω] in
theorem expectation_const (W : TapeLaw Ω) (c : ℚ) :
    W.expectation (fun _ => c) = c := by
  simp [CryptoHiddenScalarTapeAverageContract.TapeLaw.expectation, ← Finset.sum_mul, W.total]

omit [DecidableEq Ω] in
theorem expectation_add (W : TapeLaw Ω) (f g : Ω → ℚ) :
    W.expectation (fun w => f w + g w) = W.expectation f + W.expectation g := by
  simp [CryptoHiddenScalarTapeAverageContract.TapeLaw.expectation, mul_add, Finset.sum_add_distrib]

omit [DecidableEq Ω] in
theorem expectation_scale (W : TapeLaw Ω) (c : ℚ) (f : Ω → ℚ) :
    W.expectation (fun w => c * f w) = c * W.expectation f := by
  simp only [CryptoHiddenScalarTapeAverageContract.TapeLaw.expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _; ring

def heavy (a τ : Ω → ℚ) : Finset Ω := Finset.univ.filter (fun w => τ w ≤ a w)

/-- Exact variable-cutoff upper split; no division by an average threshold. -/
theorem variable_threshold_split (W : TapeLaw Ω) (a τ : Ω → ℚ)
    (ha : ∀ w, a w ≤ 1) :
    W.expectation a ≤ W.expectation τ +
      W.expectation (fun w => if w ∈ heavy a τ then 1 - τ w else 0) := by
  rw [← expectation_add]
  apply W.expectation_mono
  intro w
  by_cases h : τ w ≤ a w
  · simpa [heavy, h] using ha w
  · simp only [heavy, Finset.mem_filter, Finset.mem_univ, true_and, h, if_false, add_zero]
    exact le_of_lt (lt_of_not_ge h)

theorem heavy_mass_lower (W : TapeLaw Ω) (a : Ω → ℚ) (θ : ℚ)
    (hθ : θ < 1) (ha : ∀ w, a w ≤ 1) :
    max 0 ((W.expectation a - θ) / (1 - θ)) ≤ mass W (heavy a (fun _ => θ)) := by
  have h := variable_threshold_split W a (fun _ => θ) ha
  have he : W.expectation (fun w => if w ∈ heavy a (fun _ => θ) then 1 - θ else 0) =
      (1 - θ) * mass W (heavy a (fun _ => θ)) := by
    rw [mass, ← expectation_scale]
    congr 1; funext w; split_ifs <;> simp
  rw [expectation_const, he] at h
  apply max_le (mass_nonneg W _)
  apply (div_le_iff₀ (by linarith : 0 < 1 - θ)).mpr
  nlinarith

theorem qualifying_mass_lower_of_cap (W : TapeLaw Ω) (a τ : Ω → ℚ)
    (θ : ℚ) (hθ : θ < 1) (ha : ∀ w, a w ≤ 1) (hcap : ∀ w, τ w ≤ θ) :
    max 0 ((W.expectation a - θ) / (1 - θ)) ≤ mass W (heavy a τ) := by
  apply (heavy_mass_lower W a θ hθ ha).trans
  apply mass_mono W
  intro w hw
  simp only [heavy, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact (hcap w).trans hw

theorem variable_mass_lower (W : TapeLaw Ω) (a τ : Ω → ℚ)
    (ha : ∀ w, a w ≤ 1) (hτ : ∀ w, 0 ≤ τ w) :
    max 0 (W.expectation a - W.expectation τ) ≤ mass W (heavy a τ) := by
  have h := variable_threshold_split W a τ ha
  have hm : W.expectation (fun w => if w ∈ heavy a τ then 1 - τ w else 0) ≤
      mass W (heavy a τ) := W.expectation_mono _ _ fun w => by
    split_ifs <;> linarith [hτ w]
  exact max_le (mass_nonneg W _) (by linarith)

/-- The endpoint A=1 is handled without dividing by 1-θ. -/
theorem mass_one_of_acceptance_one (W : TapeLaw Ω) (a τ : Ω → ℚ)
    (ha : ∀ w, a w ≤ 1) (hτ : ∀ w, τ w ≤ 1) (hA : W.expectation a = 1) :
    mass W (heavy a τ) = 1 := by
  have hz : W.expectation (fun w => 1 - a w) = 0 := by
    have he : W.expectation (fun w => 1 - a w) = 1 - W.expectation a := by
      have he : (fun w => 1 - a w) = (fun w => 1 + (-1) * a w) := by funext w; ring
      rw [he, expectation_add, expectation_const, expectation_scale]; ring
    rw [he, hA]; ring
  have each : ∀ w, 0 < W.weight w → a w = 1 := by
    intro w hw
    by_contra hn
    have hp : 0 < W.expectation (fun w => 1 - a w) :=
      (W.expectation_pos_iff _ (fun w => by linarith [ha w])).mpr
        ⟨w,hw,by have := ha w; rcases lt_or_eq_of_le this with h | h
                 · linarith
                 · exact False.elim (hn h)⟩
    linarith
  calc
    mass W (heavy a τ) = W.expectation (fun _ => 1) := by
      unfold mass CryptoHiddenScalarTapeAverageContract.TapeLaw.expectation
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : W.weight w = 0
      · simp [hw]
      · have he := each w (lt_of_le_of_ne (W.nonneg w) (Ne.symm hw))
        simp [heavy, he, hτ w]
    _ = 1 := W.expectation_one

/-- A nonnegative bound on a subset may be propagated through the full original law. -/
theorem expectation_lower_on_set (W : TapeLaw Ω) (f : Ω → ℚ) (G : Finset Ω)
    (b : ℚ) (hf : ∀ w, 0 ≤ f w) (hb : ∀ w ∈ G, b ≤ f w) :
    b * mass W G ≤ W.expectation f := by
  rw [mass, ← expectation_scale]
  apply W.expectation_mono
  intro w; by_cases hw : w ∈ G
  · simpa [hw] using hb w hw
  · simpa [hw] using hf w

theorem mass_split (W : TapeLaw Ω) {G H : Finset Ω} (h : G ⊆ H) :
    mass W H = mass W G + mass W (H \ G) := by
  rw [mass, mass, mass, ← expectation_add]
  congr 1; funext w
  by_cases hg : w ∈ G
  · simp [hg,h hg]
  · by_cases hh : w ∈ H <;> simp [hg,hh]

theorem good_mass_lower (W : TapeLaw Ω) {G H : Finset Ω} (h : G ⊆ H)
    (m ε : ℚ) (hm : m ≤ mass W H) (hε : mass W (H \ G) ≤ ε) :
    max 0 (m - ε) ≤ mass W G := by
  have hs := mass_split W h
  exact max_le (mass_nonneg W _) (by linarith)
end TapeLaw

namespace TapeExperiment
variable {q k : ℕ} {A Ω S : Type} [Fact q.Prime] [AddCommGroup A]
  [Module (ZMod q) A] [DecidableEq A] [Fintype Ω] [DecidableEq Ω]

abbrev acceptance (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k) (w : Ω) : ℚ :=
  acceptanceRate (E.plan w) claim (E.model w)
def qualifying (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k) : Finset Ω :=
  TapeLaw.heavy (acceptance E claim) (fun w => (E.thresholds w).value 0)

omit [Fintype Ω] [DecidableEq Ω] in
theorem acceptance_le_one (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k) (w : Ω) :
    acceptance E claim w ≤ 1 := by
  by_cases h : (Finset.univ : Finset (SinglePathSeed (E.plan w))).Nonempty
  · exact CryptoBulletproofsIPATreeProbabilityContract.probability_le_one _ _ h
  · simp [acceptance, acceptanceRate, Prob.probability, Finset.not_nonempty_iff_eq_empty.mp h]

theorem qualifying_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (θ : ℚ) (hθ : θ < 1)
    (hcap : ∀ w, (E.thresholds w).value 0 ≤ θ) :
    max 0 ((W.expectation (acceptance E claim) - θ) / (1-θ)) ≤
      TapeLaw.mass W (qualifying E claim) :=
  TapeLaw.qualifying_mass_lower_of_cap W _ _ θ hθ (acceptance_le_one E claim) hcap

theorem averaged_lower_on_good (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (hG : G ⊆ qualifying E claim)
    (b : ℚ) (hb : ∀ w ∈ G, b ≤ protocolThresholdBound (E.plan w) (E.thresholds w)) :
    b * TapeLaw.mass W G ≤ E.averagedBound W claim := by
  apply TapeLaw.expectation_lower_on_set W _ G b (fun w => (E.guarded_range claim w).1)
  intro w hw
  have hq : E.qualifies claim w := (Finset.mem_filter.mp (hG hw)).2
  simpa [CryptoHiddenScalarTapeAverageContract.TapeExperiment.guardedBound, hq] using hb w hw

theorem averaged_lower_with_exception (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (hG : G ⊆ qualifying E claim)
    (b m ε : ℚ) (hb0 : 0 ≤ b)
    (hb : ∀ w ∈ G, b ≤ protocolThresholdBound (E.plan w) (E.thresholds w))
    (hm : m ≤ TapeLaw.mass W (qualifying E claim))
    (hε : TapeLaw.mass W (qualifying E claim \ G) ≤ ε) :
    b * max 0 (m-ε) ≤ E.averagedBound W claim :=
  (mul_le_mul_of_nonneg_left (TapeLaw.good_mass_lower W hG m ε hm hε) hb0).trans
    (averaged_lower_on_good E W claim G hG b hb)

theorem good_tapes_extract (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω) (hG : G ⊆ qualifying E claim)
    (b m ε : ℚ) (hb0 : 0 < b)
    (hb : ∀ w ∈ G, b ≤ protocolThresholdBound (E.plan w) (E.thresholds w))
    (hm : m ≤ TapeLaw.mass W (qualifying E claim))
    (hε : TapeLaw.mass W (qualifying E claim \ G) ≤ ε) (hgap : ε < m) :
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧
        F.ResultValid claim (C.extractCompressed claim f) := by
  classical
  apply E.positive_mass_extracts W claim
  exact (mul_pos hb0 (lt_max_of_lt_right (sub_pos.mpr hgap))).trans_le
    (averaged_lower_with_exception E W claim G hG b m ε hb0.le hb hm hε)
omit [DecidableEq Ω] in
/-- Global acceptance only supplies qualifying mass; b is a separate quota premise. -/
theorem global_acceptance_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (θ α b : ℚ) (hθ : θ < 1) (hb0 : 0 ≤ b)
    (hcap : ∀ w, (E.thresholds w).value 0 ≤ θ)
    (hacc : α ≤ W.expectation (acceptance E claim))
    (hb : ∀ w ∈ qualifying E claim,
      b ≤ protocolThresholdBound (E.plan w) (E.thresholds w)) :
    b * max 0 ((α-θ)/(1-θ)) ≤ E.averagedBound W claim := by
  classical
  have hm : max 0 ((α-θ)/(1-θ)) ≤ TapeLaw.mass W (qualifying E claim) := by
    apply le_trans _ (qualifying_lower E W claim θ hθ hcap)
    exact max_le_max_left _ (div_le_div_of_nonneg_right (sub_le_sub_right hacc θ)
      (by linarith : 0 ≤ 1-θ))
  exact (mul_le_mul_of_nonneg_left hm hb0).trans
    (averaged_lower_on_good E W claim _ (fun _ h => h) b hb)

omit [DecidableEq Ω] in
theorem global_success_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (θ α b : ℚ) (hθ : θ < 1) (hb0 : 0 ≤ b)
    (hcap : ∀ w, (E.thresholds w).value 0 ≤ θ)
    (hacc : α ≤ W.expectation (acceptance E claim))
    (hb : ∀ w ∈ qualifying E claim,
      b ≤ protocolThresholdBound (E.plan w) (E.thresholds w)) :
    b * max 0 ((α-θ)/(1-θ)) ≤ E.successProbability W claim := by
  classical
  exact (global_acceptance_lower E W claim θ α b hθ hb0 hcap hacc hb).trans
    (E.averaged_acquisition_lower W claim)

omit [DecidableEq Ω] in
theorem global_acceptance_extracts (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (θ α b : ℚ) (hθ : θ < 1) (hb0 : 0 < b)
    (hcap : ∀ w, (E.thresholds w).value 0 ≤ θ)
    (hacc : α ≤ W.expectation (acceptance E claim))
    (hb : ∀ w ∈ qualifying E claim,
      b ≤ protocolThresholdBound (E.plan w) (E.thresholds w)) (hgap : θ < α) :
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧
        F.ResultValid claim (C.extractCompressed claim f) := by
  classical
  apply E.positive_mass_extracts W claim
  exact (mul_pos hb0 (lt_max_of_lt_right (div_pos (sub_pos.mpr hgap)
    (sub_pos.mpr hθ)))).trans_le
    (global_acceptance_lower E W claim θ α b hθ hb0.le hcap hacc hb)
end TapeExperiment

structure CryptoHiddenScalarHeavyTapeContractSuite : Prop where
  weighted_heavy : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (W : TapeLaw Ω)
    (a : Ω → ℚ) (θ : ℚ), θ < 1 → (∀ w, a w ≤ 1) →
    max 0 ((W.expectation a - θ)/(1-θ)) ≤ TapeLaw.mass W (TapeLaw.heavy a (fun _ => θ))
  variable_split : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (W : TapeLaw Ω)
    (a τ : Ω → ℚ), (∀ w, a w ≤ 1) → W.expectation a ≤ W.expectation τ +
    W.expectation (fun w => if w ∈ TapeLaw.heavy a τ then 1-τ w else 0)

  extraction : ∀ (q k : ℕ) (A Ω S : Type) [Fact q.Prime] [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] [Fintype Ω] (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (θ α b : ℚ) (_hθ : θ < 1) (_hb0 : 0 < b)
    (_hcap : ∀ w, (E.thresholds w).value 0 ≤ θ)
    (_hacc : α ≤ W.expectation (TapeExperiment.acceptance E claim))
    (_hb : ∀ w ∈ TapeExperiment.qualifying E claim,
      b ≤ protocolThresholdBound (E.plan w) (E.thresholds w)) (_hgap : θ < α),
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧
        F.ResultValid claim (C.extractCompressed claim f)

theorem verification_suite : CryptoHiddenScalarHeavyTapeContractSuite where
  weighted_heavy := by intros; apply TapeLaw.heavy_mass_lower <;> assumption
  variable_split := by intros; apply TapeLaw.variable_threshold_split; assumption
  extraction := by intros; apply TapeExperiment.global_acceptance_extracts <;> assumption
end CryptoHiddenScalarHeavyTapeContract
