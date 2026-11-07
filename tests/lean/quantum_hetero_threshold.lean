import Verification.QuantumHeterogeneousBBPSSW
open QuantumHeterogeneousBBPSSW QuantumBBPSSWDistillation
example (F : ℝ) : heteroRecurrence F F = recurrence F := heteroRecurrence_diag F
example (x y : ℝ) : heteroRecurrence x y = heteroRecurrence y x := heteroRecurrence_symm x y
example : heteroRecurrence (3/4) (3/5) = 83/118 ∧ heteroRecurrence (3/4) (3/5) < 3/4 :=
  hetero_counterexample_three_quarters_three_fifths
example : thresholdFor (3/4) = 19/28 ∧ thresholdFor (1/2) = 1/2 := by
  norm_num [thresholdFor]
example : heteroRecurrence (1/2) (3/4) = 7/11 ∧ (1/2:ℝ) < 7/11 := by
  norm_num [heteroRecurrence, heteroTargetMass, heteroSuccessProb]
example : heteroSuccessProb 1 (-1/2) = 0 ∧ heteroTargetMass 1 (-1/2) = -1/2 := by
  norm_num [heteroSuccessProb, heteroTargetMass]
example : heteroSuccessProb 1 0 = 1/3 ∧ heteroSuccessProb 0 1 = 1/3 := by
  norm_num [heteroSuccessProb]
example {x y : ℝ} (hx : 1 / 4 < x ∧ x < 1) (hy : 1 / 4 < y ∧ y < 1) :
    max x y < heteroRecurrence x y ↔ thresholdFor x < y ∧ thresholdFor y < x :=
  hetero_strict_improve_max_iff hx hy
example {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    1/3 ≤ heteroSuccessProb x y ∧ heteroSuccessProb x y ≤ 1 := heteroSuccessProb_bounds hx hy
