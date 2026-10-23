import Verification.QuantumSteaneCodeErrorCorrectionContract

open QuantumSteaneCodeErrorCorrectionContract

set_option maxRecDepth 10000

-- Independent matrix, codeword, and decoder boundary values.
example : syndrome (unitWord 0) = ![1, 0, 0] := by decide
example : syndrome (unitWord 6) = ![1, 1, 1] := by decide
example : weight (hRow 0) = 4 := by decide
example : weight (hRow 1 + hRow 2) = 4 := by decide
example : (Finset.univ.filter rowSpace).card = 8 := rowspace_card
example : ¬ rowSpace ones := by decide
example : syndrome ones = 0 := by decide
example : decodeSyndrome (0, 0) = none := by decide
example : decodeSyndrome (![1, 0, 0], 0) = some (0, 0) := by decide
example : decodeSyndrome (0, ![1, 1, 1]) = some (1, 6) := by decide
example : decodeSyndrome (![0, 0, 1], ![0, 0, 1]) = some (2, 3) := by decide
example : decodeSyndrome (![1, 0, 0], ![0, 1, 0]) = none := by decide
example : pauliSyndrome (singleLabel (0, 4)) ≠
    pauliSyndrome (singleLabel (1, 4)) := by decide
example : pauliSyndrome (singleLabel (2, 6)) ≠ (0, 0) := by decide

-- Actual amplitude normalization and a genuine two-dimensional code space.
example : ketNormSq (encode (3 / 5) (4 / 5 * Complex.I)) = 1 := by
  rw [encoding_isometry]
  norm_num [Complex.normSq_mul]

example : encode 0 0 = 0 := by
  ext q
  simp [encode, rawEncode]

example : encode 1 0 ≠ encode 0 1 := by
  intro h
  have hp := @encoding_injective (1, 0) (0, 1) h
  have hc := congrArg Prod.fst hp
  norm_num at hc

example : ketNormSq (encode Complex.I 0) = 1 := by
  simp [encoding_isometry]

example (ψ : Ket) : Codespace ψ ↔ ∃! p : ℂ × ℂ, encode p.1 p.2 = ψ :=
  codespace_exactly_one_qubit ψ

example : ketNormSq (rawEncode 1 0) = 8 := by simp [rawEncode_norm]
example : encode 1 0 0 = normFactor := by simp [encode, rawEncode_at_zero]
example : encode 0 1 ones = normFactor := by simp [encode, rawEncode_at_ones]

-- Canonical Y phase is tested in both directions, not merely modulo phase.
example : applySingleError (2, 0) (fun q => if q = 0 then 1 else 0) (unitWord 0) =
    Complex.I := by
  change Complex.I * (sign (dot (unitWord 0) (unitWord 0 + unitWord 0)) *
    (if unitWord 0 + unitWord 0 = 0 then 1 else 0)) = Complex.I
  rw [word_add_self]
  simp [dot, sign]

example : applySingleError (2, 0) (fun q => if q = unitWord 0 then 1 else 0) 0 =
    -Complex.I := by
  simp [applySingleError, scale, xAction, zAction, unit_self_dot, sign]

example (ψ : Ket) : applySingleError (2, 5) (applySingleError (2, 5) ψ) = ψ :=
  canonical_y_involution 5 ψ

example : xAction (unitWord 0) (zAction (unitWord 0)
    (xAction (unitWord 0) (zAction (unitWord 0) (fun _ => 1)))) 0 = -1 := by
  rw [unsigned_xz_square]
  simp [scale]

-- Decoder-driven exact recovery and actual check-projector action.
example : recover (pauliSyndrome (singleLabel (0, 6)))
    (applySingleError (0, 6) (encode Complex.I (2 - Complex.I))) =
      encode Complex.I (2 - Complex.I) := single_error_correction _ _

example : recover (pauliSyndrome (singleLabel (2, 3)))
    (applySingleError (2, 3) (encode (3 / 5) (4 / 5 * Complex.I))) =
      encode (3 / 5) (4 / 5 * Complex.I) := single_error_correction _ _

example : recover (pauliSyndrome (singleLabel (1, 0)))
    (applySingleError (1, 0) (encode 0 1)) = encode 0 1 := single_error_correction _ _

example : syndromeProjection (pauliSyndrome (singleLabel (2, 4)))
    (applySingleError (2, 4) (encode Complex.I 1)) =
      applySingleError (2, 4) (encode Complex.I 1) :=
  single_error_correct_projection _ (encoding_codespace _ _)

example (ψ : Ket) : recover (0, 0) ψ = ψ := identity_exact_recovery ψ
example (e : SingleError) : recover (pauliSyndrome (singleLabel e))
    (applySingleError e 0) = 0 := single_error_correction e 0

-- All operator families, logical signs, and exact distance boundaries.
example (ψ : Ket) : stabilizerAction (0, 0) (stabilizerAction (1, 1) ψ) =
    stabilizerAction (1, 1) (stabilizerAction (0, 0) ψ) := stabilizers_commute _ _ _

example (ψ : Ket) : stabilizerAction (1, 0) (stabilizerAction (1, 2) ψ) =
    stabilizerAction (1, 2) (stabilizerAction (1, 0) ψ) := stabilizers_commute _ _ _

example (ψ : Ket) : logicalX (logicalZ ψ) = scale (-1) (logicalZ (logicalX ψ)) :=
  logical_anticommutation ψ

example : logicalX (encode 1 Complex.I) = encode Complex.I 1 := logicalX_on_encoding _ _
example : logicalZ (encode 1 Complex.I) = encode 1 (-Complex.I) := logicalZ_on_encoding _ _
example : pauliWeight logicalWeightThree = 3 := by decide
example : ¬ InCentralizer (unitWord 0 + unitWord 1, 0) := by decide
example : ¬ InCentralizer (0, unitWord 6) := by decide
example : InCentralizer (0, 0) ∧ InStabilizerLabels (0, 0) ∧ pauliWeight (0, 0) = 0 := by
  decide

example : InStabilizerLabels (hRow 0, hRow 1) ∧
    pauliWeight (hRow 0, hRow 1) = 6 := by decide

-- Two errors can alias a single error and cause an actual logical flip.
example : pauliSyndrome (unitWord 0 + unitWord 1, 0) =
    pauliSyndrome (singleLabel (0, 2)) := by decide

example : recover (pauliSyndrome (unitWord 0 + unitWord 1, 0))
    (xAction (unitWord 0 + unitWord 1) (encode 1 0)) = encode 0 1 :=
  two_error_miscorrection 1 0

example : recover (pauliSyndrome (unitWord 0 + unitWord 1, 0))
    (xAction (unitWord 0 + unitWord 1) (encode 1 0)) ≠ encode 1 0 := by
  rw [two_error_miscorrection]
  intro h
  have hp := @encoding_injective (0, 1) (1, 0) h
  have hc := congrArg Prod.fst hp
  norm_num at hc

-- A syndrome cannot reveal an unknown global phase.
example : recover (pauliSyndrome (singleLabel (0, 0)))
    (scale (-1) (applySingleError (0, 0) (encode 1 0))) = encode (-1) 0 := by
  simp only [recover, single_syndrome_decodes]
  change xAction (unitWord 0) (scale (-1) (xAction (unitWord 0) (encode 1 0))) = _
  rw [x_scale, x_involution]
  simpa using (encoding_smul (-1) 1 0).symm

example : encode (-1) 0 ≠ encode 1 0 := by
  intro h
  have hp := @encoding_injective (-1, 0) (1, 0) h
  have hc := congrArg Prod.fst hp
  norm_num at hc

-- The generic scalar argument is not automatically a unit-modulus phase.
example (x z : Word) (ψ : Ket) : pauliAction 0 x z ψ = 0 := by
  ext q
  simp [pauliAction, scale]

example : QuantumSteaneCodeErrorCorrectionSuite := verification_suite
