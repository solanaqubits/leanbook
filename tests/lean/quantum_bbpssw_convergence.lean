import Verification.QuantumBBPSSWConvergence
open QuantumBBPSSWDistillation QuantumBBPSSWConvergence Filter Topology

example : Tendsto (fidelityOrbit (3/4)) atTop (nhds 1) :=
  fidelityOrbit_tendsto_one (by norm_num) (by norm_num)
example : Tendsto (fidelityOrbit 1) atTop (nhds 1) :=
  fidelityOrbit_tendsto_one (by norm_num) (by norm_num)
example : Tendsto (fidelityOrbit 0) atTop (nhds (1/4)) :=
  fidelityOrbit_tendsto_quarter (by norm_num) (by norm_num)
example : Tendsto (fidelityOrbit (1/4)) atTop (nhds (1/4)) :=
  fidelityOrbit_tendsto_quarter (by norm_num) (by norm_num)
example : Tendsto (fidelityOrbit (3/8)) atTop (nhds (1/4)) :=
  fidelityOrbit_tendsto_quarter (by norm_num) (by norm_num)
example : StrictMono (fidelityOrbit 0) :=
  fidelityOrbit_strictMono_below_quarter (by norm_num) (by norm_num)
example : StrictAnti (fidelityOrbit (3/8)) :=
  fidelityOrbit_strictAnti_quarter_to_half (by norm_num) (by norm_num)
example : StrictMono (fidelityOrbit (3/4)) :=
  fidelityOrbit_strictMono_above_half (by norm_num) (by norm_num)
example (n : ℕ) : fidelityOrbit (1/2) n = 1/2 :=
  fidelityOrbit_fixed ((fixed_points _).mpr (Or.inr (Or.inl rfl))) n
example : recurrence (1/10) = 5/26 := by
  norm_num [recurrence, targetMass, successProbability]
example (F : ℝ) : recurrence F - 1/4 = (4*F-1)*(8*F+1)/(36*successProbability F) :=
  recurrence_sub_quarter F
example (F : ℝ) : 1 - recurrence F = 2*(1-F)*(F+2)/(9*successProbability F) :=
  one_sub_recurrence F
