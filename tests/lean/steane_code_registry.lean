import Verification.MasterSuite

open QuantumSteaneCodeErrorCorrectionContract

example : QuantumSteaneCodeErrorCorrectionSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.quantum_suite.steane_code

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumSteaneCodeErrorCorrectionSuite := r.quantum_physics_full_suite.steane_code

example (r : MasterSuite.QuantumPhysicsFullSuite) (ψ : Ket) :
    Codespace ψ ↔ ∃! p : ℂ × ℂ, encode p.1 p.2 = ψ := r.steane_code.code_coordinates ψ

example (r : MasterSuite.QuantumPhysicsFullSuite) (a b : ℂ) :
    ketNormSq (encode a b) = Complex.normSq a + Complex.normSq b :=
  r.steane_code.encoding_norm a b

example (r : MasterSuite.QuantumPhysicsFullSuite) (e : SingleError) :
    pauliSyndrome (singleLabel e) ≠ (0, 0) := r.steane_code.detection e

example (r : MasterSuite.QuantumPhysicsFullSuite) (e : SingleError) :
    decodeSyndrome (pauliSyndrome (singleLabel e)) = some e := r.steane_code.decoder e

example (r : MasterSuite.QuantumPhysicsFullSuite) (e : SingleError) (ψ : Ket) :
    recover (pauliSyndrome (singleLabel e)) (applySingleError e ψ) = ψ :=
  r.steane_code.correction e ψ

example (r : MasterSuite.QuantumPhysicsFullSuite) (ψ : Ket) :
    recover (0, 0) ψ = ψ := r.steane_code.identity_correction ψ

example (r : MasterSuite.QuantumPhysicsFullSuite) (e : SingleError) (ψ : Ket)
    (h : Codespace ψ) :
    syndromeProjection (pauliSyndrome (singleLabel e)) (applySingleError e ψ) =
      applySingleError e ψ := r.steane_code.measured_syndrome e ψ h

example (r : MasterSuite.QuantumPhysicsFullSuite) (p : BinaryPauli)
    (hc : InCentralizer p) (hn : ¬ InStabilizerLabels p) : 3 ≤ pauliWeight p :=
  r.steane_code.distance_lower p hc hn

example (r : MasterSuite.QuantumPhysicsFullSuite) :
    InCentralizer logicalWeightThree ∧ ¬ InStabilizerLabels logicalWeightThree ∧
      pauliWeight logicalWeightThree = 3 := r.steane_code.distance_upper

example (r : MasterSuite.QuantumPhysicsFullSuite) (ψ : Ket) :
    logicalX (logicalZ ψ) = scale (-1) (logicalZ (logicalX ψ)) := r.steane_code.logical_anti ψ

example (r : MasterSuite.QuantumPhysicsFullSuite) (a b : ℂ) :
    recover (pauliSyndrome (unitWord 0 + unitWord 1, 0))
      (xAction (unitWord 0 + unitWord 1) (encode a b)) = encode b a :=
  r.steane_code.multi_error_limit a b
