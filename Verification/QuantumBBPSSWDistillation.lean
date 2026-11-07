/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCliffordTwirl

/-! Ideal two-copy BBPSSW step. Pair-major ordering is (A1,B1,A2,B2).
Unnormalized branches are linear; independent preparation is not a cloning channel. -/
noncomputable section
namespace QuantumBBPSSWDistillation
open QuantumCliffordTwirl
open QuantumNoisySwapping
open QuantumRectangularSwapping
open QuantumCascadedSwapping QuantumCorrelatedMemoryBSM QuantumPersistentEnvironment
open QuantumBellDiagonalInputs QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumNoisyBellInstrument QuantumPauliDensityBridge
open QuantumBellDiagonalSwapping QuantumNoiseTransport QuantumGateNoiseComposition
open scoped BigOperators ComplexOrder Matrix Kronecker

def flip (i : FourIndex) : FourIndex := (i.1, (i.2.1 + i.1.1, i.2.2 + i.1.2))

theorem flip_involutive (i : FourIndex) : flip (flip i) = i := by
  rcases i with ⟨⟨a,b⟩,⟨c,d⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl

theorem flip_eq (i j : FourIndex) : flip i = j ↔ i = flip j := by
  constructor
  · intro h; rw [← h, flip_involutive]
  · intro h; rw [h, flip_involutive]

def biCNOT : FourDensity := fun i j => if flip i = j then 1 else 0

theorem biCNOT_left (M : FourDensity) (i j) : (biCNOT * M) i j = M (flip i) j := by
  simp [biCNOT, Matrix.mul_apply]

theorem biCNOT_right (M : FourDensity) (i j) : (M * biCNOT) i j = M i (flip j) := by
  simp [biCNOT, Matrix.mul_apply, flip_eq]

theorem biCNOT_adjoint : biCNOT.conjTranspose = biCNOT := by
  ext i j : 2
  have h : flip j = i ↔ flip i = j := by rw [flip_eq]; exact eq_comm
  simp only [biCNOT, Matrix.conjTranspose_apply, h]
  split_ifs <;> simp

theorem biCNOT_unitary : biCNOT.conjTranspose * biCNOT = 1 := by
  rw [biCNOT_adjoint]
  ext i j : 2
  rw [biCNOT_left]
  simp [biCNOT, flip_involutive, Matrix.one_apply]

def branchOp (s : PairIndex) : Matrix PairIndex FourIndex ℂ := select s * biCNOT

def branch (s : PairIndex) : KrausBranch FourIndex PairIndex :=
  ⟨Unit, inferInstance, fun _ => branchOp s⟩

theorem branch_entry (s : PairIndex) (M : FourDensity) (i j : PairIndex) :
    (branch s).map M i j = M (flip (i,s)) (flip (j,s)) := by
  change (∑ _ : Unit, branchOp s * M * (branchOp s).conjTranspose) i j = _
  rw [Fintype.sum_unique]
  have h : branchOp s * M * (branchOp s).conjTranspose =
      select s * (biCNOT * M * biCNOT.conjTranspose) * (select s).conjTranspose := by
    simp only [branchOp, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [h, selector_sandwich, biCNOT_adjoint, biCNOT_right, biCNOT_left]

def accepted : KrausBranch FourIndex PairIndex :=
  ⟨Fin 2, inferInstance, fun b => branchOp (b,b)⟩

def rejected : KrausBranch FourIndex PairIndex :=
  ⟨Fin 2, inferInstance, fun b => branchOp (b,1-b)⟩

theorem accepted_entry (M : FourDensity) (i j : PairIndex) :
    accepted.map M i j = ∑ b : Fin 2, M (flip (i,(b,b))) (flip (j,(b,b))) := by
  change (∑ b : Fin 2, branchOp (b,b) * M * (branchOp (b,b)).conjTranspose) i j = _
  have h (b : Fin 2) : branchOp (b,b) * M * (branchOp (b,b)).conjTranspose =
      (branch (b,b)).map M := by
    change _ = ∑ _ : Unit, _
    rw [Fintype.sum_unique]
    rfl
  simp only [h, Matrix.sum_apply, branch_entry]

theorem instrument_cp : IsCPMap accepted.map ∧ IsCPMap rejected.map :=
  ⟨accepted.cp, rejected.cp⟩

theorem instrument_trace (M : FourDensity) :
    (accepted.map M).trace + (rejected.map M).trace = M.trace := by
  have h : accepted.map M + rejected.map M =
      traceEnvironment (biCNOT * M * biCNOT.conjTranspose) := by
    change (∑ b : Fin 2, branchOp (b,b) * M * (branchOp (b,b)).conjTranspose) +
      (∑ b : Fin 2, branchOp (b,1-b) * M * (branchOp (b,1-b)).conjTranspose) = _
    rw [trace_environment_family]
    simp only [branchOp, Matrix.conjTranspose_mul,
      Matrix.mul_assoc, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num
    abel
  rw [← Matrix.trace_add, h, trace_environment_trace, Matrix.trace_mul_cycle,
    biCNOT_unitary, Matrix.one_mul]

/-- Fidelity-parametrized Bell weights cover the full interval [0,1]. -/
def distribution (F : ℝ) (hF : 0 ≤ F ∧ F ≤ 1) : BellDistribution where
  weight a := if a = .phiPlus then F else (1-F)/3
  nonnegative := by
    intro a
    split_ifs
    · exact hF.1
    · exact div_nonneg (sub_nonneg.mpr hF.2) (by norm_num)
  total := by rw [sum_bell]; simp; ring

def werner (F : ℝ) : PairDensity :=
  F • bellProjector .phiPlus + ((1-F)/3) •
    (bellProjector .phiMinus + bellProjector .psiPlus + bellProjector .psiMinus)

theorem werner_distribution (F : ℝ) (hF : 0 ≤ F ∧ F ≤ 1) :
    werner F = density (distribution F hF) := by
  rw [density, sum_bell]
  simp [distribution, werner, smul_add, add_assoc]

theorem werner_positive (F : ℝ) (hF : 0 ≤ F ∧ F ≤ 1) : (werner F).PosSemidef := by
  rw [werner_distribution F hF]
  exact density_positive _

def successProbability (F : ℝ) : ℝ := F^2 + 2 / 3*F*(1-F) + 5 / 9*(1-F)^2
def targetMass (F : ℝ) : ℝ := F^2 + (1-F)^2 / 9
def recurrence (F : ℝ) : ℝ := targetMass F / successProbability F

theorem probability_positive (F : ℝ) : 0 < successProbability F := by
  unfold successProbability
  nlinarith [sq_nonneg (F - 1 / 4)]

theorem recurrence_difference (F : ℝ) :
    recurrence F - F = (1-F)*(4*F-1)*(2*F-1)/(9*successProbability F) := by
  unfold recurrence targetMass
  field_simp [(probability_positive F).ne']
  unfold successProbability
  ring

theorem improves_above_threshold (F : ℝ) (h : 1 / 2 < F ∧ F < 1) : F < recurrence F := by
  have hn : 0 < (1-F)*(4*F-1)*(2*F-1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hd := div_pos hn (mul_pos (by norm_num : (0:ℝ)<9) (probability_positive F))
  rw [← recurrence_difference] at hd
  linarith

theorem improves_below_quarter (F : ℝ) (h : F < 1 / 4) : F < recurrence F := by
  have hn : 0 < (1-F)*(4*F-1)*(2*F-1) :=
    mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by linarith) (by linarith))
      (by linarith)
  have hd := div_pos hn (mul_pos (by norm_num : (0:ℝ)<9) (probability_positive F))
  rw [← recurrence_difference] at hd
  linarith

theorem decreases_between_fixed_points (F : ℝ) (h : 1 / 4 < F ∧ F < 1 / 2) :
    recurrence F < F := by
  have hn : (1-F)*(4*F-1)*(2*F-1) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by linarith) (by linarith)) (by linarith)
  have hd := div_neg_of_neg_of_pos hn
    (mul_pos (by norm_num : (0:ℝ)<9) (probability_positive F))
  rw [← recurrence_difference] at hd
  linarith



/-- Exact unnormalized Bell weights from the bilateral circuit, before twirling. -/
theorem accepted_werner_matrix (F : ℝ) :
    accepted.map (werner F ⊗ₖ werner F) =
      (targetMass F) • bellProjector .phiPlus +
      (2*F*((1-F)/3)) • bellProjector .phiMinus +
      (2*((1-F)/3)^2) • (bellProjector .psiPlus + bellProjector .psiMinus) := by
  ext i j : 2
  rw [accepted_entry]
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [Fin.sum_univ_two, Fin.add_def, flip, Matrix.kroneckerMap_apply,
      werner, targetMass, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      bellProjector, purePairDensity, Matrix.vecMulVec, bellKet] <;>
    ring_nf <;> norm_num [bellCoeff_sq, bellCoeff_four] <;> ring

theorem accepted_probability (F : ℝ) :
    (accepted.map (werner F ⊗ₖ werner F)).trace = (successProbability F : ℂ) := by
  rw [accepted_werner_matrix]
  simp only [Matrix.trace_add, Matrix.trace_smul, bell_projector_trace]
  simp [Complex.real_smul, successProbability, targetMass]
  ring

theorem accepted_target_mass (F : ℝ) :
    targetOverlap (accepted.map (werner F ⊗ₖ werner F)) = (targetMass F : ℂ) := by
  rw [accepted_werner_matrix]
  simp [targetOverlap_add, targetOverlap_real_smul, projector_overlap]

theorem normalized_fidelity (F : ℝ) :
    (targetOverlap ((successProbability F : ℂ)⁻¹ •
      accepted.map (werner F ⊗ₖ werner F))).re = recurrence F := by
  rw [← Complex.ofReal_inv, Complex.coe_smul, targetOverlap_real_smul,
    accepted_target_mass]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [recurrence, div_eq_mul_inv, mul_comm]

theorem fixed_points (F : ℝ) : recurrence F = F ↔ F = 1 / 4 ∨ F = 1 / 2 ∨ F = 1 := by
  have h := recurrence_difference F
  constructor
  · intro he
    rw [he, sub_self] at h
    have hz : (1-F)*(4*F-1)*(2*F-1) = 0 :=
      (div_eq_zero_iff).mp h.symm |>.resolve_right
        (mul_ne_zero (by norm_num) (probability_positive F).ne')
    rcases mul_eq_zero.mp hz with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · right; right; linarith
      · left; linarith
    · right; left; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num [recurrence, targetMass, successProbability]



/-- The accepted instrument remains linear and CP before conditioning. -/
def purified (M : FourDensity) : PairDensity := twirl (accepted.map M)

theorem purified_cp : IsCPMap purified := cp_comp twirl accepted.map twirl_cp accepted.cp

theorem purified_add (M N : FourDensity) : purified (M+N) = purified M + purified N := by
  unfold purified
  have h : accepted.map (M+N) = accepted.map M + accepted.map N :=
    accepted.linear.map_add M N
  rw [h, twirl_add]

theorem purified_smul (c : ℂ) (M : FourDensity) : purified (c • M) = c • purified M := by
  unfold purified
  have h : accepted.map (c • M) = c • accepted.map M := accepted.linear.map_smul c M
  rw [h, twirl_smul]

theorem purified_trace_balance (M : FourDensity) :
    (purified M).trace + (rejected.map M).trace = M.trace := by
  rw [purified, twirl_trace, instrument_trace]

theorem recurrence_bounds (F : ℝ) (hF : 0 ≤ F ∧ F ≤ 1) :
    0 ≤ recurrence F ∧ recurrence F ≤ 1 := by
  have hp := probability_positive F
  have hg : 0 ≤ F*(1-F) := mul_nonneg hF.1 (sub_nonneg.mpr hF.2)
  constructor
  · exact div_nonneg (by unfold targetMass; positivity) hp.le
  · apply (div_le_one hp).mpr
    unfold targetMass successProbability
    nlinarith [sq_nonneg (1-F)]

theorem purified_werner (F : ℝ) :
    purified (werner F ⊗ₖ werner F) =
      (successProbability F : ℂ) • werner (recurrence F) := by
  rw [purified, twirl_formula, accepted_probability, accepted_target_mass]
  have hr : successProbability F * recurrence F = targetMass F := by
    unfold recurrence
    exact mul_div_cancel₀ _ (probability_positive F).ne'
  have hs : successProbability F * ((1-recurrence F)/3) =
      (successProbability F-targetMass F)/3 := by
    rw [← mul_div_assoc, mul_sub, mul_one, hr]
  simp only [werner, ← Complex.coe_smul, smul_add, smul_smul,
    ← Complex.ofReal_mul, hr, hs]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]

theorem purified_conditional (F : ℝ) :
    (successProbability F : ℂ)⁻¹ • purified (werner F ⊗ₖ werner F) =
      werner (recurrence F) := by
  rw [purified_werner, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (probability_positive F).ne'), one_smul]

theorem purified_conditional_positive (F : ℝ) (hF : 0 ≤ F ∧ F ≤ 1) :
    ((successProbability F : ℂ)⁻¹ • purified (werner F ⊗ₖ werner F)).PosSemidef := by
  rw [purified_conditional]
  exact werner_positive _ (recurrence_bounds F hF)

theorem purified_conditional_trace (F : ℝ) (hF : 0 ≤ F ∧ F ≤ 1) :
    ((successProbability F : ℂ)⁻¹ • purified (werner F ⊗ₖ werner F)).trace = 1 := by
  rw [purified_conditional, werner_distribution _ (recurrence_bounds F hF)]
  exact density_trace _

structure QuantumBBPSSWDistillationSuite : Prop where
  balance : ∀ M, (purified M).trace + (rejected.map M).trace = M.trace
  matrix_refinement : ∀ F, purified (werner F ⊗ₖ werner F) =
    (successProbability F : ℂ) • werner (recurrence F)
  threshold : ∀ F, 1 / 2 < F ∧ F < 1 → F < recurrence F
  fixed : ∀ F, recurrence F = F ↔ F = 1 / 4 ∨ F = 1 / 2 ∨ F = 1

theorem verification_suite : QuantumBBPSSWDistillationSuite :=
  ⟨purified_trace_balance, purified_werner, improves_above_threshold, fixed_points⟩

end QuantumBBPSSWDistillation
