import Verification.MasterSuite

open QuantumStateAvailabilityContract

example : QuantumStateAvailabilitySuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.quantum_state_availability

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumStateAvailabilitySuite := r.quantum_physics_full_suite.quantum_state_availability

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumStateAvailabilitySuite := r.quantum_state_availability

example (r : MasterSuite.QuantumPhysicsFullSuite) (m : BellMeasurement) (ψ : QubitState) :
    applyCorrection m (bobBranch m ψ) = ψ := r.quantum_state_availability.recovery m ψ

example (r : MasterSuite.QuantumPhysicsFullSuite) (m : BellMeasurement) (ψ : QubitState)
    (h : Normalized ψ) : outcomeProbability m ψ = 1 / 4 :=
  r.quantum_state_availability.born_weights m ψ h

example (r : MasterSuite.QuantumPhysicsFullSuite) (m : BellMeasurement) (ψ : QubitState)
    (h : Normalized ψ) : senderReduced (normalizedPost m ψ) = mixedHalf :=
  r.quantum_state_availability.sender_local m ψ h

example (r : MasterSuite.QuantumPhysicsFullSuite) (ψ : QubitState) (h : Normalized ψ) :
    unconditionedBob ψ = mixedHalf := r.quantum_state_availability.classical_requirement ψ h

example (r : MasterSuite.QuantumPhysicsFullSuite) (s : QSAStatus) (ψ : QubitState) :
    (qsaTransition s ψ).isSome = true ↔
      s.pairCertified = true ∧ s.reportedOutcome.isSome = true :=
  r.quantum_state_availability.gate_availability s ψ

example (r : MasterSuite.QuantumPhysicsFullSuite) (s : QSAStatus) (m : BellMeasurement)
    (ψ : QubitState) (hp : s.pairCertified = true) (hm : s.reportedOutcome = some m) :
    qsaTransition s (bobBranch m ψ) = some ψ :=
  r.quantum_state_availability.gate_recovery s m ψ hp hm

example (r : MasterSuite.QuantumPhysicsFullSuite) (ψ : QubitState) :
    decodeNV (encodeNV ψ) = ψ := r.quantum_state_availability.nv_roundtrip ψ
