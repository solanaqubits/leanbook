import Verification.QuantumHeterogeneousBBPSSW
open QuantumHeterogeneousBBPSSW QuantumBBPSSWDistillation QuantumBBPSSWConvergence
example : swapFidelity (4/5) = 73/100 ∧ elemFidelity (4/5) = 17/20 := by
  norm_num [swapFidelity, elemFidelity]
example : recurrence (73/100) = 2705/3524 := by
  norm_num [recurrence, targetMass, successProbability]
example : (73/100:ℝ) < 2705/3524 ∧ (2705/3524:ℝ) < 17/20 := by norm_num
example : ∃ n, elemFidelity (4/5) < fidelityOrbit (swapFidelity (4/5)) n :=
  exists_purification_depth_exceeding_elemFidelity (by norm_num) (by norm_num) (by norm_num)
namespace DepthRegression
theorem depth0 : fidelityOrbit (73/100) 0 = 73/100 := by
  rfl
theorem depth1 : fidelityOrbit (73/100) 1 = 2705/3524 := by
  rw [show 1 = 0+1 from rfl, fidelityOrbit_succ, depth0]
  norm_num [recurrence, targetMass, successProbability]
theorem depth2 : fidelityOrbit (73/100) 2 = 3695777/4583300 := by
  rw [show 2 = 1+1 from rfl, fidelityOrbit_succ, depth1]
  norm_num [recurrence, targetMass, successProbability]
theorem depth3 : fidelityOrbit (73/100) 3 = 6873144765505/8141550923524 := by
  rw [show 3 = 2+1 from rfl, fidelityOrbit_succ, depth2]
  norm_num [recurrence, targetMass, successProbability]
theorem depth4 : fidelityOrbit (73/100) 4 =
    23709440271666641852174977/26972943138329845628509700 := by
  rw [show 4 = 3+1 from rfl, fidelityOrbit_succ, depth3]
  norm_num [recurrence, targetMass, successProbability]
example : fidelityOrbit (73/100) 2 < 17/20 := by rw [depth2]; norm_num
example : fidelityOrbit (73/100) 3 < 17/20 := by rw [depth3]; norm_num
example : (17/20:ℝ) < fidelityOrbit (73/100) 4 := by rw [depth4]; norm_num
example : ∀ n < 4, fidelityOrbit (73/100) n < 17/20 := by
  intro n hn
  interval_cases n <;> norm_num [depth0, depth1, depth2, depth3]
end DepthRegression
