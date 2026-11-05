import Verification.QuantumBellDiagonalSwapping

open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellCircuitRefinement QuantumNoisyBellInstrument
open QuantumGeneralBellReadout QuantumBellDiagonalInputs QuantumBellDiagonalSwapping
open scoped BigOperators ComplexOrder Kronecker

-- The ket theorem retains a negative phase which the density theorem may discard.
example : readoutBranch .phiMinus (productKet .psiPlus .phiPlus) =
    -(1 / 2 : ℂ) • bellKet .psiMinus :=
  branch_amplitude .psiPlus .phiPlus .phiMinus

example (p q : BellDistribution) : inputDensity p q = density p ⊗ₖ density q :=
  input_density_tensor p q

example (p q : BellDistribution) :
    (inputDensity p q).PosSemidef ∧ (inputDensity p q).trace = 1 :=
  ⟨input_positive p q, input_trace p q⟩

example (p q : BellDistribution) (m : BellMeasurement) : mixedBornProbability p q m = 1 / 4 :=
  mixed_born_probability p q m

example (a b m r : BellMeasurement) :
    purePairDensity (correctOuter r (readoutBranch m (productKet a b))) =
      (1 / 4 : ℝ) • bellProjector (bellXor (bellXor (bellXor a b) m) r) :=
  raw_corrected_density a b m r

example (p q : BellDistribution) (model : Readout) :
    QuantumBellDiagonalSwapping.circuitDensity p q model = acceptedDensity p q model :=
  circuit_density_sound p q model

example (p q : BellDistribution) (model : Readout) :
    eventMass p q model = QuantumSelectiveSwapping.acceptedMass model :=
  event_mass_formula p q model

example (p q : BellDistribution) (model : Readout)
    (h : 0 < QuantumSelectiveSwapping.acceptedMass model) :
    (conditionalState p q model h).matrix.PosSemidef ∧
    (conditionalState p q model h).matrix.trace = 1 :=
  ⟨(conditionalState p q model h).positive, (conditionalState p q model h).trace_one⟩

example (model : Readout) (h : 0 < QuantumSelectiveSwapping.acceptedMass model) :
    (conditionalState (pointDistribution .phiPlus) (pointDistribution .phiPlus) model h).matrix =
      (QuantumSelectiveSwapping.conditionalState model h).matrix := ideal_inputs_conditional model h

example (q : BellDistribution) : idealDensity uniformDistribution q = maximallyMixed :=
  uniform_input_erases_ideal_output q

-- Fully mixed and pure visibility limits are included in the same exact matrix law.
example (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) :
    idealDensity (isotropicDistribution 0 (by norm_num)) (isotropicDistribution v hv) =
      density (isotropicDistribution (0 * v)
        (visibility_product_valid 0 v (by norm_num) hv)) :=
  isotropic_visibility_product 0 v (by norm_num) hv

example : targetOverlap (idealDensity
    (isotropicDistribution (1 / 2) (by norm_num))
    (isotropicDistribution (1 / 2) (by norm_num))) = (7 / 16 : ℂ) := by
  rw [isotropic_output_fidelity]
  norm_num

example : targetOverlap (idealDensity
    (isotropicDistribution 1 (by norm_num))
    (isotropicDistribution 1 (by norm_num))) = 1 := by
  rw [isotropic_output_fidelity]
  norm_num

example : targetOverlap (density (halfError false)) = targetOverlap (density (halfError true)) := by
  exact scalar_fidelity_insufficient.1.trans scalar_fidelity_insufficient.2.1.symm

example : targetOverlap (idealDensity (halfError false) (halfError false)) ≠
    targetOverlap (idealDensity (halfError true) (halfError false)) := by
  rw [scalar_fidelity_insufficient.2.2.1, scalar_fidelity_insufficient.2.2.2]
  norm_num

example (p q : BellDistribution) (model : Readout)
    (h : QuantumSelectiveSwapping.acceptedMass model = 0) : acceptedDensity p q model = 0 :=
  null_event_density p q model h

example (model : Readout)
    (h : QuantumSelectiveSwapping.acceptedMass model = 0)
    (hpos : 0 < QuantumSelectiveSwapping.acceptedMass model) : False := by
  linarith
