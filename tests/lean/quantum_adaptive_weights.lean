import Verification.QuantumAdaptiveWernerCascade
open QuantumAdaptiveWernerCascade QuantumCascadeReduction QuantumCentralDepolarization
open QuantumStateAvailabilityContract
open scoped BigOperators
noncomputable section
private def oneV : Visibility := ⟨1, by norm_num, le_rfl⟩
private def zeroV : Visibility := ⟨0, le_rfl, by norm_num⟩
private def schedule : Schedule :=
  ⟨fun _ => oneV, fun _ => oneV, fun r => if r = .phiPlus then oneV else zeroV⟩
private def biased : Efficiency :=
  ⟨fun r => if r = .phiPlus then 1 else 1 / 2,
    by intro r; split_ifs <;> norm_num, by intro r; split_ifs <;> norm_num⟩
example : totalSuccessProb perfectEfficiency (fun _ => perfectEfficiency) = 1 :=
  perfect_total_probability
example : totalSuccessProb closedEfficiency (fun _ => perfectEfficiency) = 0 :=
  closed_first_probability _
example : totalSuccessProb perfectEfficiency (fun _ => closedEfficiency) = 0 :=
  closed_second_probability _
example : meanAlpha schedule = 1 / 4 := by
  rw [meanAlpha, QuantumNoisyBellInstrument.sum_bell]
  have h1 : BellMeasurement.phiMinus ≠ .phiPlus := by decide
  have h2 : BellMeasurement.psiPlus ≠ .phiPlus := by decide
  have h3 : BellMeasurement.psiMinus ≠ .phiPlus := by decide
  norm_num [h1, h2, h3, schedule, Schedule.alpha,
    QuantumNoisyVisibility.multiplyVisibility, oneV, zeroV]
example : weightedAlpha schedule biased (fun _ => perfectEfficiency) = 2 / 5 := by
  have h1 : BellMeasurement.phiMinus ≠ .phiPlus := by decide
  have h2 : BellMeasurement.psiPlus ≠ .phiPlus := by decide
  have h3 : BellMeasurement.psiMinus ≠ .phiPlus := by decide
  have hc : Fintype.card BellMeasurement = 4 := by decide
  norm_num [h1, h2, h3, hc, weightedAlpha, totalSuccessProb, branchSuccessWeight,
    QuantumNoisyBellInstrument.sum_bell, biased, perfectEfficiency, schedule,
    Schedule.alpha, QuantumNoisyVisibility.multiplyVisibility, oneV, zeroV]
example : branchSuccessWeight perfectEfficiency (fun _ => perfectEfficiency) .phiPlus =
    1 / 4 := perfect_branch_weight _
example : wernerFidelity 1 = 1 ∧ wernerFidelity (1 / 4) = 7 / 16 := by
  norm_num [wernerFidelity]
