import Verification.MasterSuite

open scoped ComplexOrder

open QuantumStateAvailabilityContract QuantumEntanglementSwappingPurificationContract

example : QuantumEntanglementSwappingPurificationSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.entanglement_swapping_purification

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumEntanglementSwappingPurificationSuite :=
  r.quantum_physics_full_suite.entanglement_swapping_purification

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumEntanglementSwappingPurificationSuite := r.entanglement_swapping_purification

example (r : MasterSuite.QuantumPhysicsFullSuite) (m : BellMeasurement) :
    swapOutcomeProbability m = 1 / 4 := r.entanglement_swapping_purification.probability m

example (r : MasterSuite.QuantumPhysicsFullSuite) (m : BellMeasurement) :
    correctOuter m (swappedOuter m) = bellKet .phiPlus :=
  r.entanglement_swapping_purification.correction m

example (r : MasterSuite.QuantumPhysicsFullSuite) (F : ℚ) (h : 1 / 2 < F ∧ F < 1) :
    F < purifiedFidelity F := r.entanglement_swapping_purification.improvement F h

example (r : MasterSuite.QuantumPhysicsFullSuite) (F : ℚ) (h : 0 ≤ F ∧ F ≤ 1) :
    1 / 2 ≤ acceptedMass F ∧ acceptedMass F ≤ 1 :=
  r.entanglement_swapping_purification.success F h

example (r : MasterSuite.QuantumPhysicsFullSuite) (F : ℚ) :
    purifiedFidelity F = F ↔ F = 0 ∨ F = 1 / 2 ∨ F = 1 :=
  r.entanglement_swapping_purification.fixed F

example (r : MasterSuite.QuantumPhysicsFullSuite) (F : ℚ) (h : 0 ≤ F ∧ F ≤ 1) :
    (phaseDensity F).PosSemidef := r.entanglement_swapping_purification.density_positive F h

example (r : MasterSuite.QuantumPhysicsFullSuite) (F : ℚ) :
    (filteredDensity F).trace = 1 := (r.entanglement_swapping_purification.filtered_valid F).2.1
