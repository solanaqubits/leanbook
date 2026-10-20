/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarHeavyTapeContract

/-! Decidable recursive arithmetic margins and a computable finite minimum remove
an externally postulated positive quota constant. Acceptance and positive tape
mass remain separate premises. Original plans, microseeds and extractors are kept. -/
namespace CryptoHiddenScalarQuotaMarginContract
set_option backward.isDefEq.respectTransparency false
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarForkLocalDensityContract
open CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarTapeAverageContract
open CryptoHiddenScalarHeavyTapeContract

variable {q k : ℕ} {A Ω S : Type}

/-- Leaf certificates impose no artificial quota four. -/
def treeMarginCertificate : {d : ℕ} → TreePlan q S d → ThresholdProfile → Prop
  | _, .leaf, _ => True
  | _, .node law T child, h => treeMarginCertificate child h.tail ∧ 4 ≤ T ∧
      3 * law.beta < thresholdDensity h (treeThresholdBound child h.tail)

instance treeMarginDecidable : {d : ℕ} → (p : TreePlan q S d) → (h : ThresholdProfile) →
    Decidable (treeMarginCertificate p h)
  | _, .leaf, _ => inferInstanceAs (Decidable True)
  | _, .node _law _T child, h =>
    letI := treeMarginDecidable child h.tail
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def etaMarginCertificate (p : EtaPlan q S k) (h : ThresholdProfile) : Prop :=
  treeMarginCertificate p.tree h.tail ∧ 2 ≤ p.budget ∧
    p.law.beta < thresholdDensity h (treeThresholdBound p.tree h.tail)

instance (p : EtaPlan q S k) (h : ThresholdProfile) :
    Decidable (etaMarginCertificate p h) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def protocolMarginCertificate (p : ProtocolPlan q S k) (h : ThresholdProfile) : Prop :=
  etaMarginCertificate p.eta h.tail ∧ 3 ≤ p.budget ∧
    2 * p.law.beta < thresholdDensity h (etaThresholdBound p.eta h.tail)

instance (p : ProtocolPlan q S k) (h : ThresholdProfile) :
    Decidable (protocolMarginCertificate p h) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem tree_certificate_positive (p : TreePlan q S k) (h : ThresholdProfile)
    (hc : treeMarginCertificate p h) : 0 < treeThresholdBound p h := by
  cases p with
  | leaf => norm_num [treeThresholdBound]
  | node law T child =>
    exact linear_quota_positive 4 T (by decide) hc.2.1 _ law.beta
      (threshold_density_range h _ (tree_threshold_range child h.tail)).2
      law.beta_nonneg (by simpa using hc.2.2)

theorem eta_certificate_positive (p : EtaPlan q S k) (h : ThresholdProfile)
    (hc : etaMarginCertificate p h) : 0 < etaThresholdBound p h := by
  exact linear_quota_positive 2 p.budget (by decide) hc.2.1 _ p.law.beta
    (threshold_density_range h _ (tree_threshold_range p.tree h.tail)).2
    p.law.beta_nonneg (by simpa using hc.2.2)

theorem protocol_certificate_positive (p : ProtocolPlan q S k) (h : ThresholdProfile)
    (hc : protocolMarginCertificate p h) : 0 < protocolThresholdBound p h := by
  exact linear_quota_positive 3 p.budget (by decide) hc.2.1 _ p.law.beta
    (threshold_density_range h _ (eta_threshold_range p.eta h.tail)).2
    p.law.beta_nonneg (by simpa using hc.2.2)

/-- Total exact minimum; independent of tape weights and acceptance. -/
def finiteRootLower (E : TapeExperiment q A Ω S k) (G : Finset Ω) : ℚ :=
  if hg : G.Nonempty then
    (G.image (fun w => protocolThresholdBound (E.plan w) (E.thresholds w))).min'
      (hg.image _)
  else 0

@[simp] theorem finiteRootLower_empty (E : TapeExperiment q A Ω S k) :
    finiteRootLower E ∅ = 0 := by simp [finiteRootLower]

theorem finiteRootLower_le (E : TapeExperiment q A Ω S k) (G : Finset Ω)
    (w : Ω) (hw : w ∈ G) :
    finiteRootLower E G ≤ protocolThresholdBound (E.plan w) (E.thresholds w) := by
  rw [finiteRootLower, dif_pos ⟨w,hw⟩]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩)

theorem finiteRootLower_positive (E : TapeExperiment q A Ω S k) (G : Finset Ω)
    (hg : G.Nonempty)
    (hc : ∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) :
    0 < finiteRootLower E G := by
  rw [finiteRootLower, dif_pos hg, Finset.lt_min'_iff]
  intro y hy
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
  exact protocol_certificate_positive _ _ (hc w hw)

theorem finiteRootLower_range (E : TapeExperiment q A Ω S k) (G : Finset Ω) :
    0 ≤ finiteRootLower E G ∧ finiteRootLower E G ≤ 1 := by
  by_cases hg : G.Nonempty
  · have hm := Finset.min'_mem (G.image (fun w => protocolThresholdBound (E.plan w)
      (E.thresholds w))) (hg.image _)
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hm
    rw [finiteRootLower, dif_pos hg, ← he]
    exact protocol_threshold_range _ _
  · simp [finiteRootLower,hg]

section Weighted
variable [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A]
  [Fintype Ω] [DecidableEq Ω]

/-- Positive mass, not mere nonemptiness, is needed for the probability bridge. -/
theorem nonempty_of_mass_pos (W : TapeLaw Ω) (G : Finset Ω)
    (hm : 0 < TapeLaw.mass W G) : G.Nonempty := by
  by_contra h
  have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [he, TapeLaw.mass, CryptoHiddenScalarTapeAverageContract.TapeLaw.expectation] at hm

theorem certified_average_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω)
    (hg : G ⊆ TapeExperiment.qualifying E claim) :
    finiteRootLower E G * TapeLaw.mass W G ≤ E.averagedBound W claim :=
  TapeExperiment.averaged_lower_on_good E W claim G hg _ (finiteRootLower_le E G)

theorem certified_success_lower (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hm : 0 < TapeLaw.mass W G)
    (hc : ∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) :
    0 < finiteRootLower E G * TapeLaw.mass W G ∧
    finiteRootLower E G * TapeLaw.mass W G ≤ E.averagedBound W claim ∧
    E.averagedBound W claim ≤ E.successProbability W claim :=
  ⟨mul_pos (finiteRootLower_positive E G (nonempty_of_mass_pos W G hm) hc) hm,
   certified_average_lower E W claim G hg, E.averaged_acquisition_lower W claim⟩

theorem certified_extracts (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (G : Finset Ω)
    (hg : G ⊆ TapeExperiment.qualifying E claim)
    (hm : 0 < TapeLaw.mass W G)
    (hc : ∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) :
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧
        F.ResultValid claim (C.extractCompressed claim f) := by
  have h := certified_success_lower E W claim G hg hm hc
  exact E.positive_mass_extracts W claim (h.1.trans_le h.2.1)

/-- Global acceptance supplies qualifying mass; certificates supply the quota margin. -/
theorem global_qualifying_mass_pos (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (θ α : ℚ) (hθ : θ < 1)
    (hcap : ∀ w, (E.thresholds w).value 0 ≤ θ)
    (hacc : α ≤ W.expectation (TapeExperiment.acceptance E claim)) (hgap : θ < α) :
    0 < TapeLaw.mass W (TapeExperiment.qualifying E claim) := by
  apply lt_of_lt_of_le _ (TapeExperiment.qualifying_lower E W claim θ hθ hcap)
  exact lt_max_of_lt_right (div_pos (by linarith) (by linarith))

omit [DecidableEq Ω] in
theorem global_certified_extracts (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (θ α : ℚ) (hθ : θ < 1)
    (hcap : ∀ w, (E.thresholds w).value 0 ≤ θ)
    (hacc : α ≤ W.expectation (TapeExperiment.acceptance E claim)) (hgap : θ < α)
    (hc : ∀ w ∈ TapeExperiment.qualifying E claim,
      protocolMarginCertificate (E.plan w) (E.thresholds w)) :
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧
        F.ResultValid claim (C.extractCompressed claim f) :=
  by
  classical
  exact certified_extracts E W claim _ (fun _ hw => hw)
    (global_qualifying_mass_pos E W claim θ α hθ hcap hacc hgap) hc
end Weighted

structure CryptoHiddenScalarQuotaMarginContractSuite : Prop where
  positivity : ∀ (q k : ℕ) (S : Type) (p : ProtocolPlan q S k) (h : ThresholdProfile),
    protocolMarginCertificate p h → 0 < protocolThresholdBound p h
  minimum : ∀ (q k : ℕ) (A Ω S : Type) (E : TapeExperiment q A Ω S k) (G : Finset Ω),
    G.Nonempty → (∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) →
    0 < finiteRootLower E G
  extraction : ∀ (q k : ℕ) (A Ω S : Type) [Fact q.Prime] [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] [Fintype Ω] [DecidableEq Ω]
    (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω) (claim : F.Claim q A k)
    (G : Finset Ω), G ⊆ TapeExperiment.qualifying E claim → 0 < TapeLaw.mass W G →
    (∀ w ∈ G, protocolMarginCertificate (E.plan w) (E.thresholds w)) →
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧ F.ResultValid claim (C.extractCompressed claim f)

theorem verification_suite : CryptoHiddenScalarQuotaMarginContractSuite where
  positivity := by intros; apply protocol_certificate_positive; assumption
  minimum := by intros; apply finiteRootLower_positive <;> assumption
  extraction := by intros; apply certified_extracts <;> assumption
end CryptoHiddenScalarQuotaMarginContract
