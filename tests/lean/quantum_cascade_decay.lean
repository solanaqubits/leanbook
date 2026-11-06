import Verification.QuantumCascadeReduction

noncomputable section
open QuantumCentralDepolarization QuantumCascadeReduction Filter
open scoped Topology

def vOne : Visibility := ⟨1, by norm_num, by norm_num⟩
def vHalf : Visibility := ⟨1/2, by norm_num, by norm_num⟩
def vZero : Visibility := ⟨0, by norm_num, by norm_num⟩

def halfParams := ofVisibilities vOne vOne vHalf

def fullLoss := ofVisibilities vZero vOne vOne

-- A positive input above any alleged improvement threshold still decays.
example : wernerTransition halfParams 1 = 1/2 ∧
    wernerFidelity (wernerTransition halfParams 1) = 5/8 := by
  norm_num [halfParams, vOne, vHalf, ofVisibilities, alphaParam,
    wernerTransition, wernerFidelity]

example : (wernerTransition halfParams)^[3] 1 = 1/8 := by
  rw [cascaded_iteration]
  norm_num [halfParams, ofVisibilities, vOne, vHalf, alphaParam]

example (w : ℝ) : wernerTransition halfParams w = w ↔ w = 0 := by
  apply unique_fixed_point_at_zero
  norm_num [halfParams, ofVisibilities, vOne, vHalf, alphaParam]

-- The endpoint alpha=0 reaches 1/4 in one step; alpha=1 preserves every input.
example : wernerFidelity (wernerTransition fullLoss 1) = 1/4 := by
  norm_num [fullLoss, ofVisibilities, vZero, vOne, alphaParam,
    wernerTransition, wernerFidelity]

example (w : ℝ) : wernerTransition (ofVisibilities vOne vOne vOne) w = w := by
  apply lossless_identity
  norm_num [ofVisibilities, vOne, alphaParam]

-- The limit is separately kernel-checked, not inferred from the finite identity.
example : Tendsto (fun n : ℕ => wernerFidelity ((wernerTransition halfParams)^[n] 1))
    atTop (𝓝 (1/4)) := by
  apply fidelity_tends_to_quarter
  norm_num [halfParams, ofVisibilities, vOne, vHalf, alphaParam]

example (n : ℕ) : (1/4 : ℝ) ≤
    wernerFidelity ((wernerTransition halfParams)^[n] 1) :=
  fidelity_above_quarter halfParams 1 (by norm_num) n

example : runVisibility [halfParams, fullLoss] 1 = 0 := by
  rw [finite_schedule_product]
  norm_num [halfParams, fullLoss, ofVisibilities, vOne, vHalf, vZero, alphaParam]
