import Verification.OptospintronicTransducerContract
import Lean.Elab.Tactic.Omega

open OptospintronicTransducerContract

private def center : SpinReservoirState 1 := ⟨0, by norm_num, by norm_num⟩
private def upper : SpinReservoirState 1 := ⟨1, by norm_num, by norm_num⟩
private def lower : SpinReservoirState 1 := ⟨-1, by norm_num, by norm_num⟩
private def empty : SpinReservoirState 0 := ⟨0, by norm_num, by norm_num⟩
private def half : SpinReservoirState 1 := ⟨1 / 2, by norm_num, by norm_num⟩
private def rHalf : OpticalPulse := ⟨1, .RightCircular, 1 / 2, by norm_num, by norm_num⟩
private def lHalf : OpticalPulse := ⟨1, .LeftCircular, 1 / 2, by norm_num, by norm_num⟩
private def rTwo : OpticalPulse := ⟨2, .RightCircular, 1, by norm_num, by norm_num⟩
private def lTwo : OpticalPulse := ⟨2, .LeftCircular, 1, by norm_num, by norm_num⟩
private def rOne : OpticalPulse := ⟨1, .RightCircular, 1, by norm_num, by norm_num⟩
private def linear : OpticalPulse := ⟨100, .Linear, 1, by norm_num, by norm_num⟩
private def noCoupling : OpticalPulse := ⟨100, .RightCircular, 0, by norm_num, by norm_num⟩
private def noPhotons : OpticalPulse := ⟨0, .LeftCircular, 1, by norm_num, by norm_num⟩

example : polarizationSign .LeftCircular = -1 := rfl
example : polarizationSign .RightCircular = 1 := rfl
example : polarizationSign .Linear = 0 := rfl
example : couplingBudget rHalf = 1 / 2 := by norm_num [couplingBudget, rHalf]
example : (transferMomentum rHalf center).spinZ = 1 / 2 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, rHalf, center]
example : (transferMomentum lHalf center).spinZ = -1 / 2 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, lHalf, center]
-- The mean transfer need not be an integer, even for one incident photon.
example : ¬ ∃ k : ℤ, (k : ℚ) = (transferMomentum rHalf center).spinZ - center.spinZ := by
  intro ⟨k, hk⟩
  norm_num [transferMomentum, momentumDelta, couplingBudget, rHalf, center] at hk
  have hq : (2 : ℚ) * (k : ℚ) = 1 := by linarith
  have hi : (2 : ℤ) * k = 1 := by exact_mod_cast hq
  omega
example : (transferMomentum rTwo center).spinZ = 1 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, rTwo, center]
example : (transferMomentum lTwo center).spinZ = -1 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, lTwo, center]
example : (transferMomentum rOne center).spinZ = 1 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, rOne, center]
example : (transferMomentum rTwo lower).spinZ = 1 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, rTwo, lower]
example : (transferMomentum lTwo upper).spinZ = -1 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, lTwo, upper]
example : (transferMomentum rHalf upper) = upper := by
  ext; norm_num [transferMomentum, momentumDelta, couplingBudget, rHalf, upper]
example : (transferMomentum lHalf lower) = lower := by
  ext; norm_num [transferMomentum, momentumDelta, couplingBudget, lHalf, lower]
example : ¬ upper.spinZ < (transferMomentum rHalf upper).spinZ := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, rHalf, upper]
example : ¬ (transferMomentum lHalf lower).spinZ < lower.spinZ := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, lHalf, lower]
example : transferMomentum linear half = half := linear_polarization_invariance _ _ rfl
example : transferMomentum noCoupling half = half := zero_efficiency_neutrality _ _ rfl
example : transferMomentum noPhotons half = half := zero_photon_identity _ _ rfl
example : transferMomentum rTwo empty = empty := zero_capacity_identity _ _
example : (transferMomentum rHalf half).spinZ = 1 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, rHalf, half]
example : (transferMomentum lHalf half).spinZ = 0 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, lHalf, half]
example : signedIncidentMomentum rTwo = 2 := by
  norm_num [signedIncidentMomentum, polarizationSign, rTwo]
example : requestedMomentum rHalf = 1 / 2 := by
  norm_num [requestedMomentum, polarizationSign, couplingBudget, rHalf]
example : uncoupledMomentum rHalf = 1 / 2 := by
  norm_num [uncoupledMomentum, polarizationSign, rHalf]
example : saturationRemainder center rTwo = 1 := by
  norm_num [saturationRemainder, requestedMomentum, momentumDelta, polarizationSign,
    couplingBudget, center, rTwo]
example : saturationRemainder center lTwo = -1 := by
  norm_num [saturationRemainder, requestedMomentum, momentumDelta, polarizationSign,
    couplingBudget, center, lTwo]
example : saturationRemainder center rHalf = 0 := by
  norm_num [saturationRemainder, requestedMomentum, momentumDelta, polarizationSign,
    couplingBudget, center, rHalf]
example : opticalOutputMomentum center rTwo = 1 := by
  rw [optical_output_eq_incident_sub_delta]
  norm_num [signedIncidentMomentum, momentumDelta, polarizationSign, couplingBudget, center, rTwo]
example : opticalOutputMomentum center lTwo = -1 := by
  rw [optical_output_eq_incident_sub_delta]
  norm_num [signedIncidentMomentum, momentumDelta, polarizationSign, couplingBudget, center, lTwo]
example : opticalOutputMomentum center rHalf = 1 / 2 := by
  rw [optical_output_eq_incident_sub_delta]
  norm_num [signedIncidentMomentum, momentumDelta, polarizationSign, couplingBudget, center, rHalf]
example : opticalOutputMomentum upper rHalf = 1 := by
  rw [optical_output_eq_incident_sub_delta]
  norm_num [signedIncidentMomentum, momentumDelta, polarizationSign, couplingBudget, upper, rHalf]
example : opticalOutputMomentum half noCoupling = 100 := by
  rw [optical_output_eq_incident_sub_delta]
  norm_num [signedIncidentMomentum, momentumDelta, polarizationSign, couplingBudget,
    half, noCoupling]
example : opticalOutputMomentum empty rTwo = 2 := by
  rw [optical_output_eq_incident_sub_delta]
  norm_num [signedIncidentMomentum, momentumDelta, polarizationSign, couplingBudget, empty, rTwo]
example : saturationRemainder half linear = 0 ∧ opticalOutputMomentum half linear = 0 :=
  linear_remainder_zero _ _ rfl
-- Reservoir-only conservation fails when saturation blocks part of the requested transfer.
example : center.spinZ + signedIncidentMomentum rTwo ≠ (transferMomentum rTwo center).spinZ := by
  norm_num [signedIncidentMomentum, polarizationSign, transferMomentum, momentumDelta,
    couplingBudget, center, rTwo]
example : center.spinZ + signedIncidentMomentum rTwo =
    (transferMomentum rTwo center).spinZ + opticalOutputMomentum center rTwo :=
  angular_momentum_conservation _ _
example (Smax : ℕ) (s : SpinReservoirState Smax) (p : OpticalPulse) :
    |(transferMomentum p s).spinZ - s.spinZ| ≤ couplingBudget p := transferred_momentum_bound _ _
example (Smax : ℕ) (s : SpinReservoirState Smax) (p : OpticalPulse) :
    |opticalOutputMomentum s p| ≤ (p.photonCount : ℚ) := optical_output_magnitude_bound _ _
example : (transferMomentum rHalf center).spinZ = center.spinZ + couplingBudget rHalf :=
  right_unsaturated_transfer _ _ rfl (by norm_num [couplingBudget, rHalf, center])
example : (transferMomentum lHalf center).spinZ = center.spinZ - couplingBudget lHalf :=
  left_unsaturated_transfer _ _ rfl (by norm_num [couplingBudget, lHalf, center])
-- Distinct pulse order gives distinct saturated states; no commutation is asserted.
example : (transferMomentum lTwo (transferMomentum rTwo center)).spinZ = -1 ∧
    (transferMomentum rTwo (transferMomentum lTwo center)).spinZ = 1 := by
  norm_num [transferMomentum, momentumDelta, couplingBudget, rTwo, lTwo, center]
example : ¬ (0 : ℚ) ≤ -1 := by norm_num
example : ¬ (2 : ℚ) ≤ 1 := by norm_num
example : OptospintronicTransducerSuite := verification_suite
