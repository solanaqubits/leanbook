/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumBBPSSWDistillation
import Mathlib.Topology.Instances.Real.Lemmas

/-! Ideal BBPSSW iteration and the weight of a complete binary resource tree.
Each node consumes two independent copies; no unknown-state cloning is assumed. -/
noncomputable section
namespace QuantumBBPSSWConvergence
open QuantumBBPSSWDistillation QuantumEntanglementSwappingPurificationContract
open QuantumBellDiagonalInputs QuantumNoisySwapping QuantumNoisyBellInstrument
open Filter Topology
open scoped BigOperators ComplexOrder Matrix Kronecker

theorem recurrence_sub_quarter (F : ℝ) :
    recurrence F - 1 / 4 = (4*F-1)*(8*F+1)/(36*successProbability F) := by
  unfold recurrence targetMass
  field_simp [(probability_positive F).ne']
  unfold successProbability
  ring

theorem one_sub_recurrence (F : ℝ) :
    1 - recurrence F = 2*(1-F)*(F+2)/(9*successProbability F) := by
  unfold recurrence targetMass
  field_simp [(probability_positive F).ne']
  unfold successProbability
  ring

theorem recurrence_lt_one {F : ℝ} (h0 : 0 ≤ F) (h1 : F < 1) :
    recurrence F < 1 := by
  have hn : 0 < 2*(1-F)*(F+2) := by positivity
  have h := div_pos hn (mul_pos (by norm_num : (0:ℝ)<9) (probability_positive F))
  rw [← one_sub_recurrence] at h
  linarith

theorem recurrence_invariant_above_half {F : ℝ} (h0 : 1 / 2 < F) (h1 : F < 1) :
    1 / 2 < recurrence F ∧ recurrence F < 1 :=
  ⟨lt_trans h0 (improves_above_threshold F ⟨h0,h1⟩),
    recurrence_lt_one (by linarith) h1⟩

theorem recurrence_invariant_quarter_to_half {F : ℝ}
    (h0 : 1 / 4 < F) (h1 : F < 1 / 2) :
    1 / 4 < recurrence F ∧ recurrence F < 1 / 2 := by
  have hn : 0 < (4*F-1)*(8*F+1) := mul_pos (by linarith) (by linarith)
  have h := div_pos hn (mul_pos (by norm_num : (0:ℝ)<36) (probability_positive F))
  rw [← recurrence_sub_quarter] at h
  exact ⟨by linarith, lt_trans (decreases_between_fixed_points F ⟨h0,h1⟩) h1⟩

theorem recurrence_invariant_below_quarter {F : ℝ} (h0 : 0 ≤ F) (h1 : F < 1 / 4) :
    0 < recurrence F ∧ recurrence F < 1 / 4 := by
  have hn : (4*F-1)*(8*F+1) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have h := div_neg_of_neg_of_pos hn
    (mul_pos (by norm_num : (0:ℝ)<36) (probability_positive F))
  rw [← recurrence_sub_quarter] at h
  exact ⟨lt_of_le_of_lt h0 (improves_below_quarter F h1), by linarith⟩

def fidelityOrbit (F : ℝ) (n : ℕ) : ℝ := (recurrence^[n]) F

@[simp] theorem fidelityOrbit_zero (F : ℝ) : fidelityOrbit F 0 = F := rfl

theorem fidelityOrbit_succ (F : ℝ) (n : ℕ) :
    fidelityOrbit F (n+1) = recurrence (fidelityOrbit F n) :=
  Function.iterate_succ_apply' _ _ _

theorem fidelityOrbit_fixed {F : ℝ} (h : recurrence F = F) (n : ℕ) :
    fidelityOrbit F n = F := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fidelityOrbit_succ, ih, h]

theorem fidelityOrbit_bounds {F : ℝ} (h : 0 ≤ F ∧ F ≤ 1) (n : ℕ) :
    0 ≤ fidelityOrbit F n ∧ fidelityOrbit F n ≤ 1 := by
  induction n with
  | zero => exact h
  | succ n ih => rw [fidelityOrbit_succ]; exact recurrence_bounds _ ih

theorem fidelityOrbit_above_half {F : ℝ} (h0 : 1 / 2 < F) (h1 : F < 1) (n : ℕ) :
    1 / 2 < fidelityOrbit F n ∧ fidelityOrbit F n < 1 := by
  induction n with
  | zero => exact ⟨h0,h1⟩
  | succ n ih => rw [fidelityOrbit_succ]; exact recurrence_invariant_above_half ih.1 ih.2

theorem fidelityOrbit_quarter_to_half {F : ℝ}
    (h0 : 1 / 4 < F) (h1 : F < 1 / 2) (n : ℕ) :
    1 / 4 < fidelityOrbit F n ∧ fidelityOrbit F n < 1 / 2 := by
  induction n with
  | zero => exact ⟨h0,h1⟩
  | succ n ih =>
    rw [fidelityOrbit_succ]; exact recurrence_invariant_quarter_to_half ih.1 ih.2

theorem fidelityOrbit_below_quarter {F : ℝ} (h0 : 0 ≤ F) (h1 : F < 1 / 4) (n : ℕ) :
    0 ≤ fidelityOrbit F n ∧ fidelityOrbit F n < 1 / 4 := by
  induction n with
  | zero => exact ⟨h0,h1⟩
  | succ n ih =>
    rw [fidelityOrbit_succ]
    exact ⟨(recurrence_invariant_below_quarter ih.1 ih.2).1.le,
      (recurrence_invariant_below_quarter ih.1 ih.2).2⟩

theorem fidelityOrbit_strictMono_above_half {F : ℝ} (h0 : 1 / 2 < F) (h1 : F < 1) :
    StrictMono (fidelityOrbit F) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [fidelityOrbit_succ]
  exact improves_above_threshold _ (fidelityOrbit_above_half h0 h1 n)

theorem fidelityOrbit_strictAnti_quarter_to_half {F : ℝ}
    (h0 : 1 / 4 < F) (h1 : F < 1 / 2) : StrictAnti (fidelityOrbit F) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [fidelityOrbit_succ]
  exact decreases_between_fixed_points _ (fidelityOrbit_quarter_to_half h0 h1 n)

theorem fidelityOrbit_strictMono_below_quarter {F : ℝ} (h0 : 0 ≤ F) (h1 : F < 1 / 4) :
    StrictMono (fidelityOrbit F) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [fidelityOrbit_succ]
  exact improves_below_quarter _ (fidelityOrbit_below_quarter h0 h1 n).2

theorem continuous_recurrence : Continuous recurrence := by
  have hn : Continuous targetMass := by unfold targetMass; fun_prop
  have hd : Continuous successProbability := by unfold successProbability; fun_prop
  exact hn.div hd (fun F => (probability_positive F).ne')

/-- Any orbit limit is a genuine fixed point, by continuity and the shifted sequence. -/
theorem orbit_limit_fixed {F L : ℝ}
    (h : Tendsto (fidelityOrbit F) atTop (nhds L)) : recurrence L = L := by
  have hs : Tendsto (fun n => fidelityOrbit F (n+1)) atTop (nhds L) :=
    (tendsto_add_atTop_iff_nat 1).mpr h
  have hc := continuous_recurrence.continuousAt.tendsto.comp h
  simp only [fidelityOrbit_succ] at hs
  exact tendsto_nhds_unique hc hs

theorem fidelityOrbit_tendsto_one {F : ℝ} (h0 : 1 / 2 < F) (h1 : F ≤ 1) :
    Tendsto (fidelityOrbit F) atTop (nhds 1) := by
  rcases lt_or_eq_of_le h1 with hlt | rfl
  · have hm := (fidelityOrbit_strictMono_above_half h0 hlt).monotone
    have hb : BddAbove (Set.range (fidelityOrbit F)) :=
      ⟨1, by rintro _ ⟨n,rfl⟩; exact (fidelityOrbit_above_half h0 hlt n).2.le⟩
    have ht := tendsto_atTop_ciSup hm hb
    have hl : F ≤ ⨆ n, fidelityOrbit F n := by
      simpa using le_ciSup hb 0
    rcases (fixed_points _).mp (orbit_limit_fixed ht) with hq | hh | ho
    · linarith
    · linarith
    · rwa [ho] at ht
  · have hf : recurrence 1 = 1 := (fixed_points 1).mpr (Or.inr (Or.inr rfl))
    have he : fidelityOrbit 1 = fun _ => 1 := funext (fidelityOrbit_fixed hf)
    rw [he]
    exact tendsto_const_nhds

theorem fidelityOrbit_tendsto_quarter {F : ℝ} (h0 : 0 ≤ F) (h1 : F < 1 / 2) :
    Tendsto (fidelityOrbit F) atTop (nhds (1 / 4)) := by
  rcases lt_trichotomy F (1/4) with hlo | heq | hhi
  · have hm := (fidelityOrbit_strictMono_below_quarter h0 hlo).monotone
    have hb : BddAbove (Set.range (fidelityOrbit F)) :=
      ⟨1/4, by rintro _ ⟨n,rfl⟩; exact (fidelityOrbit_below_quarter h0 hlo n).2.le⟩
    have ht := tendsto_atTop_ciSup hm hb
    have hu : (⨆ n, fidelityOrbit F n) ≤ 1/4 :=
      ciSup_le (fun n => (fidelityOrbit_below_quarter h0 hlo n).2.le)
    rcases (fixed_points _).mp (orbit_limit_fixed ht) with hq | hh | ho
    · rwa [hq] at ht
    · linarith
    · linarith
  · subst F
    have hf : recurrence (1/4) = 1/4 := (fixed_points _).mpr (Or.inl rfl)
    have he : fidelityOrbit (1/4) = fun _ => 1/4 := funext (fidelityOrbit_fixed hf)
    rw [he]
    exact tendsto_const_nhds
  · have hm := (fidelityOrbit_strictAnti_quarter_to_half hhi h1).antitone
    have hb : BddBelow (Set.range (fidelityOrbit F)) :=
      ⟨1/4, by rintro _ ⟨n,rfl⟩; exact (fidelityOrbit_quarter_to_half hhi h1 n).1.le⟩
    have ht := tendsto_atTop_ciInf hm hb
    have hu : (⨅ n, fidelityOrbit F n) ≤ F := by simpa using ciInf_le hb 0
    rcases (fixed_points _).mp (orbit_limit_fixed ht) with hq | hh | ho
    · rwa [hq] at ht
    · linarith
    · linarith

/-- All nodes must succeed; each subtree is independently prepared. -/
def treeMatrix (F : ℝ) : ℕ → PairDensity
  | 0 => werner F
  | n+1 => purified (treeMatrix F n ⊗ₖ treeMatrix F n)

def treeProbability (F : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => treeProbability F n ^ 2 * successProbability (fidelityOrbit F n)

theorem treeProbability_pos (F : ℝ) (n : ℕ) : 0 < treeProbability F n := by
  induction n with
  | zero => norm_num [treeProbability]
  | succ n ih => exact mul_pos (pow_pos ih 2) (probability_positive _)

theorem treeProbability_closed_form (F : ℝ) (n : ℕ) :
    treeProbability F n =
      ∏ k ∈ Finset.range n, successProbability (fidelityOrbit F k) ^ (2 ^ (n-1-k)) := by
  induction n with
  | zero => simp [treeProbability]
  | succ n ih =>
    rw [treeProbability, ih, Finset.prod_range_succ, ← Finset.prod_pow]
    have hprod :
        (∏ k ∈ Finset.range n, (successProbability (fidelityOrbit F k) ^
          (2 ^ (n-1-k))) ^ 2) =
        ∏ k ∈ Finset.range n, successProbability (fidelityOrbit F k) ^ (2 ^ (n+1-1-k)) := by
      apply Finset.prod_congr rfl
      intro k hk
      have he : n+1-1-k = (n-1-k)+1 := by have := Finset.mem_range.mp hk; omega
      rw [← pow_mul, he, pow_succ]
    rw [hprod]
    simp

theorem treeProbability_two (F : ℝ) :
    treeProbability F 2 = successProbability F ^ 2 * successProbability (recurrence F) := by
  simp [treeProbability, fidelityOrbit]

theorem treeMatrix_eq_werner (F : ℝ) (n : ℕ) :
    treeMatrix F n = (treeProbability F n : ℂ) • werner (fidelityOrbit F n) := by
  induction n with
  | zero => simp [treeMatrix, treeProbability]
  | succ n ih =>
    rw [treeMatrix, ih, Matrix.smul_kronecker, Matrix.kronecker_smul,
      smul_smul, purified_smul, purified_werner, smul_smul, fidelityOrbit_succ]
    congr 1
    simp only [treeProbability, Complex.ofReal_mul, pow_two]

theorem treeMatrix_conditional (F : ℝ) (n : ℕ) :
    (treeProbability F n : ℂ)⁻¹ • treeMatrix F n = werner (fidelityOrbit F n) := by
  rw [treeMatrix_eq_werner, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (treeProbability_pos F n).ne'), one_smul]

theorem successProbability_le_one {F : ℝ} (h : 0 ≤ F ∧ F ≤ 1) :
    successProbability F ≤ 1 := by
  unfold successProbability
  nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]

theorem treeProbability_le_one {F : ℝ} (h : 0 ≤ F ∧ F ≤ 1) (n : ℕ) :
    treeProbability F n ≤ 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := (treeProbability_pos F n).le
    have hs : treeProbability F n ^ 2 ≤ 1 := by nlinarith
    exact mul_le_one₀ hs (probability_positive _).le
      (successProbability_le_one (fidelityOrbit_bounds h n))

theorem werner_trace (F : ℝ) : (werner F).trace = 1 := by
  simp only [werner, Matrix.trace_add, Matrix.trace_smul, bell_projector_trace]
  simp [Complex.real_smul]
  ring

theorem treeMatrix_trace (F : ℝ) (n : ℕ) :
    (treeMatrix F n).trace = (treeProbability F n : ℂ) := by
  rw [treeMatrix_eq_werner, Matrix.trace_smul, werner_trace, smul_eq_mul, mul_one]

theorem treeMatrix_positive {F : ℝ} (h : 0 ≤ F ∧ F ≤ 1) (n : ℕ) :
    (treeMatrix F n).PosSemidef := by
  rw [treeMatrix_eq_werner, Complex.coe_smul]
  exact (werner_positive _ (fidelityOrbit_bounds h n)).smul (treeProbability_pos F n).le

theorem treeMatrix_conditional_positive {F : ℝ} (h : 0 ≤ F ∧ F ≤ 1) (n : ℕ) :
    ((treeProbability F n : ℂ)⁻¹ • treeMatrix F n).PosSemidef := by
  rw [treeMatrix_conditional]
  exact werner_positive _ (fidelityOrbit_bounds h n)

theorem treeMatrix_conditional_trace (F : ℝ) (n : ℕ) :
    ((treeProbability F n : ℂ)⁻¹ • treeMatrix F n).trace = 1 := by
  rw [treeMatrix_conditional, werner_trace]

structure QuantumBBPSSWConvergenceSuite : Prop where
  distills : ∀ F, 1/2 < F → F ≤ 1 → Tendsto (fidelityOrbit F) atTop (nhds 1)
  mixes : ∀ F, 0 ≤ F → F < 1/2 → Tendsto (fidelityOrbit F) atTop (nhds (1/4))
  tree : ∀ F n, treeMatrix F n = (treeProbability F n : ℂ) • werner (fidelityOrbit F n)
  positive_weight : ∀ F n, 0 < treeProbability F n

theorem verification_suite : QuantumBBPSSWConvergenceSuite :=
  ⟨fun _ => fidelityOrbit_tendsto_one, fun _ => fidelityOrbit_tendsto_quarter,
    treeMatrix_eq_werner, treeProbability_pos⟩

end QuantumBBPSSWConvergence
