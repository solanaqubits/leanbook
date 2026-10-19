/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarThresholdQuotaContract

/-! Finite weighted tapes of one adversary, with conditional plan laws on dependent
seed spaces. Guarded threshold expectations bound actual acquisition. Positivity
provides an existential positive-mass run and witness-or-relation extraction,
not a search algorithm or a polynomial-time guarantee. -/
namespace CryptoHiddenScalarTapeAverageContract
set_option backward.isDefEq.respectTransparency false
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarSinglePathContract
open CryptoHiddenScalarThresholdQuotaContract

/-- Exact rational probability law; zero-mass tapes are permitted. -/
structure TapeLaw (Ω : Type) [Fintype Ω] where
  weight : Ω → ℚ
  nonneg : ∀ w, 0 ≤ weight w
  total : ∑ w, weight w = 1

namespace TapeLaw
variable {Ω : Type} [Fintype Ω]
def expectation (W : TapeLaw Ω) (f : Ω → ℚ) : ℚ := ∑ w, W.weight w * f w

theorem expectation_nonneg (W : TapeLaw Ω) (f : Ω → ℚ) (hf : ∀ w, 0 ≤ f w) :
    0 ≤ W.expectation f := Finset.sum_nonneg fun w _ => mul_nonneg (W.nonneg w) (hf w)

theorem expectation_mono (W : TapeLaw Ω) (f g : Ω → ℚ) (h : ∀ w, f w ≤ g w) :
    W.expectation f ≤ W.expectation g :=
  Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (W.nonneg w)

theorem expectation_one (W : TapeLaw Ω) : W.expectation (fun _ => 1) = 1 := by
  simpa [expectation] using W.total

theorem expectation_pos_iff (W : TapeLaw Ω) (f : Ω → ℚ) (hf : ∀ w, 0 ≤ f w) :
    0 < W.expectation f ↔ ∃ w, 0 < W.weight w ∧ 0 < f w := by
  rw [expectation, Finset.sum_pos_iff_of_nonneg (fun w _ => mul_nonneg (W.nonneg w) (hf w))]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw⟩
    rcases mul_pos_iff.mp hw with h | h
    · exact ⟨w,h⟩
    · exact False.elim ((not_lt_of_ge (W.nonneg w)) h.1)
  · rintro ⟨w, hw, hfw⟩
    exact ⟨w, mul_pos hw hfw⟩

/-- Sequential tape/seed sampling, not a uniform law on the disjoint union. -/
def jointMass (W : TapeLaw Ω) (Seed : Ω → Type) [∀ w, Fintype (Seed w)]
    (v : Sigma Seed) : ℚ := W.weight v.1 / Fintype.card (Seed v.1)

theorem jointMass_nonneg (W : TapeLaw Ω) (Seed : Ω → Type) [∀ w, Fintype (Seed w)]
    (v : Sigma Seed) : 0 ≤ W.jointMass Seed v :=
  div_nonneg (W.nonneg v.1) (Nat.cast_nonneg _)

theorem jointMass_pos_iff (W : TapeLaw Ω) (Seed : Ω → Type) [∀ w, Fintype (Seed w)]
    [∀ w, Nonempty (Seed w)] (v : Sigma Seed) :
    0 < W.jointMass Seed v ↔ 0 < W.weight v.1 := by
  exact div_pos_iff_of_pos_right (by exact_mod_cast Fintype.card_pos (α := Seed v.1))

theorem jointMass_fiber (W : TapeLaw Ω) (Seed : Ω → Type) [∀ w, Fintype (Seed w)]
    [∀ w, Nonempty (Seed w)] (w : Ω) :
    ∑ v : Seed w, W.jointMass Seed ⟨w,v⟩ = W.weight w := by
  change (∑ _ : Seed w, W.weight w / (Fintype.card (Seed w) : ℚ)) = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem jointMass_total (W : TapeLaw Ω) (Seed : Ω → Type) [∀ w, Fintype (Seed w)]
    [∀ w, Nonempty (Seed w)] : ∑ v : Sigma Seed, W.jointMass Seed v = 1 := by
  rw [Fintype.sum_sigma]
  simp_rw [W.jointMass_fiber Seed]
  exact W.total

/-- Exact event probability on the dependent joint space. -/
def jointRate (W : TapeLaw Ω) (Seed : Ω → Type) [∀ w, Fintype (Seed w)]
    (event : (w : Ω) → Seed w → Bool) : ℚ :=
  ∑ v : Sigma Seed, if event v.1 v.2 then W.jointMass Seed v else 0

theorem jointRate_eq_average (W : TapeLaw Ω) (Seed : Ω → Type)
    [∀ w, Fintype (Seed w)] [∀ w, DecidableEq (Seed w)]
    (event : (w : Ω) → Seed w → Bool) :
    W.jointRate Seed event = W.expectation (fun w => eventRate (event w)) := by
  rw [jointRate, Fintype.sum_sigma]
  unfold expectation
  apply Finset.sum_congr rfl
  intro w _
  change (∑ v : Seed w, if event w v then W.weight w / (Fintype.card (Seed w) : ℚ) else 0) = _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [eventRate, Prob.probability, Finset.inter_univ, Finset.card_univ]
  ring
end TapeLaw

/-- A single transition function and initial memory, with the tape varied explicitly.
The plan (including budgets and microseed types) may depend on the tape. -/
structure TapeExperiment (q : ℕ) (A Ω S : Type) (k : ℕ) where
  initial : S
  step : Ω → Snapshot q S → Request q → Option (Packet q A × S × ℕ)
  plan : Ω → ProtocolPlan q S k
  thresholds : Ω → ThresholdProfile

namespace TapeExperiment
variable {q k : ℕ} {A Ω S : Type}
def model (E : TapeExperiment q A Ω S k) (w : Ω) : AdversaryModel q A Ω S :=
  ⟨w, E.initial, E.step⟩
abbrev Seed (E : TapeExperiment q A Ω S k) (w : Ω) := (E.plan w).Seed

variable [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A]

def qualifies (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k) (w : Ω) : Prop :=
  (E.thresholds w).value 0 ≤ acceptanceRate (E.plan w) claim (E.model w)
instance (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k) (w : Ω) :
    Decidable (E.qualifies claim w) := inferInstanceAs (Decidable (_ ≤ _))

/-- Failed acceptance thresholds contribute zero, even if the unguarded bound is positive. -/
def guardedBound (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k) (w : Ω) : ℚ :=
  if E.qualifies claim w then protocolThresholdBound (E.plan w) (E.thresholds w) else 0

theorem guarded_range (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k) (w : Ω) :
    0 ≤ E.guardedBound claim w ∧ E.guardedBound claim w ≤ 1 := by
  unfold guardedBound
  split_ifs
  · exact protocol_threshold_range _ _
  · norm_num

theorem guarded_pos_iff (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k) (w : Ω) :
    0 < E.guardedBound claim w ↔ E.qualifies claim w ∧
      0 < protocolThresholdBound (E.plan w) (E.thresholds w) := by
  unfold guardedBound
  split_ifs with h <;> simp [h]

def success (E : TapeExperiment q A Ω S k) (claim : F.Claim q A k)
    (w : Ω) (v : E.Seed w) : Bool :=
  (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome.isOk

theorem guarded_acquisition_lower (E : TapeExperiment q A Ω S k)
    (claim : F.Claim q A k) (w : Ω) :
    E.guardedBound claim w ≤ eventRate (E.success claim w) := by
  unfold guardedBound
  split_ifs with h
  · exact threshold_acquisition_lower _ _ _ _ h
  · exact (eventRate_range _).1

variable [Fintype Ω]
def averagedBound (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω) (claim : F.Claim q A k) : ℚ :=
  W.expectation (E.guardedBound claim)
def successProbability (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) : ℚ := W.jointRate E.Seed (E.success claim)

theorem success_probability_eq_average (E : TapeExperiment q A Ω S k)
    (W : TapeLaw Ω) (claim : F.Claim q A k) :
    E.successProbability W claim = W.expectation (fun w => eventRate (E.success claim w)) :=
  W.jointRate_eq_average _ _

theorem averaged_acquisition_lower (E : TapeExperiment q A Ω S k)
    (W : TapeLaw Ω) (claim : F.Claim q A k) :
    E.averagedBound W claim ≤ E.successProbability W claim := by
  rw [success_probability_eq_average]
  exact W.expectation_mono _ _ (E.guarded_acquisition_lower claim)

theorem averaged_range (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) :
    0 ≤ E.averagedBound W claim ∧ E.averagedBound W claim ≤ 1 := by
  constructor
  · exact W.expectation_nonneg _ fun w => (E.guarded_range claim w).1
  · calc
      E.averagedBound W claim ≤ W.expectation (fun _ => 1) :=
        W.expectation_mono _ _ fun w => (E.guarded_range claim w).2
      _ = 1 := W.expectation_one

theorem averaged_pos_iff (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) :
    0 < E.averagedBound W claim ↔
      ∃ w, 0 < W.weight w ∧ E.qualifies claim w ∧
      0 < protocolThresholdBound (E.plan w) (E.thresholds w) := by
  rw [averagedBound, W.expectation_pos_iff _ (fun w => (E.guarded_range claim w).1)]
  simp_rw [E.guarded_pos_iff]

/-- Positive lower expectation supplies an actual run of positive joint mass.
The conclusion retains the existing witness-or-generator-relation dichotomy. -/
theorem positive_mass_extracts (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω)
    (claim : F.Claim q A k) (hb : 0 < E.averagedBound W claim) :
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧ F.ResultValid claim (C.extractCompressed claim f) :=
    by
  obtain ⟨w, hw, ha, hp⟩ := (E.averaged_pos_iff W claim).mp hb
  obtain ⟨v, f, hf, hprov, hres⟩ := threshold_positive_extracts (E.plan w) (E.thresholds w)
    claim (E.model w) ha hp
  exact ⟨w, v, (W.jointMass_pos_iff E.Seed ⟨w,v⟩).mpr hw, f, hf, hprov, hres⟩
end TapeExperiment

structure CryptoHiddenScalarTapeAverageContractSuite : Prop where
  finite_positivity : ∀ (Ω : Type) [Fintype Ω] (W : TapeLaw Ω) (f : Ω → ℚ),
    (∀ w, 0 ≤ f w) → (0 < W.expectation f ↔ ∃ w, 0 < W.weight w ∧ 0 < f w)
  acquisition : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S : Type) [Fintype Ω] (k : ℕ)
    (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω) (claim : F.Claim q A k),
    E.averagedBound W claim ≤ E.successProbability W claim
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S : Type) [Fintype Ω] (k : ℕ)
    (E : TapeExperiment q A Ω S k) (W : TapeLaw Ω) (claim : F.Claim q A k),
    0 < E.averagedBound W claim →
    ∃ w, ∃ v : E.Seed w, 0 < W.jointMass E.Seed ⟨w,v⟩ ∧ ∃ f,
      (acquireCompressedFork claim (E.model w) ((E.plan w).decode (E.model w) v)).outcome =
        .ok f ∧ ForkProvenance (E.model w) f ∧ F.ResultValid claim (C.extractCompressed claim f)

theorem verification_suite : CryptoHiddenScalarTapeAverageContractSuite where
  finite_positivity := fun _ _ => TapeLaw.expectation_pos_iff
  acquisition := fun _ _ _ _ _ _ _ _ _ _ => TapeExperiment.averaged_acquisition_lower
  extraction := fun _ _ _ _ _ _ _ _ _ _ => TapeExperiment.positive_mass_extracts
end CryptoHiddenScalarTapeAverageContract
