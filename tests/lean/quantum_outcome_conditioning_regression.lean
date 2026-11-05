import Verification.QuantumNullConditioning

open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGeneralBellReadout (Readout)
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumNullConditioning
open scoped BigOperators ComplexOrder Matrix

-- The rejection outcome is CP even with an entangled two-dimensional ancilla.
example (model : Readout)
    (R : Matrix (Fin 2 × FourIndex) (Fin 2 × FourIndex) ℂ) (h : R.PosSemidef) :
    (liftMap 2 (outcomeMap model none) R).PosSemidef := outcome_cp model none 2 R h

example (model : Readout) (r : BellMeasurement)
    (R : Matrix (Fin 3 × FourIndex) (Fin 3 × FourIndex) ℂ) (h : R.PosSemidef) :
    (liftMap 3 (reportedMap model r) R).PosSemidef := reported_cp model r 3 R h

example (model : Readout) (ρ : FourState) :
    (∑ o : Outcome, outcomeProbability model o ρ) = 1 := outcome_probability_total model ρ

example (model : Readout) (ρ : FourState) :
    outcomeProbability model none ρ + acceptanceProbability model ρ = 1 := by
  rw [reject_probability]
  ring

example (M : FourDensity) :
    outcomeMap (QuantumSelectiveSwapping.biasedReadout false) none M = 0 :=
  full_detection_no_reject _ (by intro m; rfl) M

-- The PSD premise is essential: trace zero alone does not imply matrix zero.
def indefiniteMatrix : PairDensity := Matrix.diagonal fun i =>
  if i = (0,0) then 1 else if i = (1,1) then -1 else 0

example : indefiniteMatrix.trace = 0 ∧ indefiniteMatrix ≠ 0 := by
  constructor
  · norm_num [indefiniteMatrix, Matrix.trace_diagonal, Fintype.sum_prod_type, Fin.sum_univ_two]
  · intro h
    have hentry := congrArg (fun M : PairDensity => M (0,0) (0,0)) h
    norm_num [indefiniteMatrix, Matrix.diagonal_apply] at hentry

example : ¬ indefiniteMatrix.PosSemidef := by
  intro h
  have hdiag := h.diag_nonneg (i := (1,1))
  norm_num [indefiniteMatrix, Matrix.diagonal_apply, Complex.le_def] at hdiag

-- At perfect readout, the impossible GHZ message is the zero sentinel, not a state.
example : outcomeConditional QuantumBellDiagonalSwapping.perfectReadout
    (some .psiPlus) ghzState = 0 := ghz_ideal_report_null.2

example : (outcomeConditional QuantumBellDiagonalSwapping.perfectReadout
    (some .psiPlus) ghzState).trace ≠ 1 := by
  rw [ghz_ideal_report_null.2, Matrix.trace_zero]
  norm_num

-- Noise can forge the same label even while its true physical branch remains impossible.
example : microMap alwaysPsiReadout .psiPlus .psiPlus ghzState.matrix = 0 :=
  ghz_psi_micro_null alwaysPsiReadout .psiPlus

example : outcomeProbability alwaysPsiReadout (some .psiPlus) ghzState = 1 :=
  zero_true_branch_nonzero_report.2

example : outcomeMap alwaysPsiReadout (some .psiPlus) ghzState.matrix ≠ 0 := by
  intro h
  have hz := (outcome_zero_iff alwaysPsiReadout (some .psiPlus) ghzState).mpr h
  rw [zero_true_branch_nonzero_report.2] at hz
  norm_num at hz

example (model : Readout) (ρ : FourState) :
    (∑ r ∈ Finset.univ.filter (fun r => 0 < outcomeProbability model (some r) ρ),
      outcomeProbability model (some r) ρ • outcomeConditional model (some r) ρ) =
      acceptanceProbability model ρ • acceptedConditional model ρ := by
  rw [positive_reported_barycenter, accepted_reconstruct]

example (model : Readout) (ρ : FourState) (h : 0 < acceptanceProbability model ρ) :
    (conditionalState model ρ h).matrix =
      ∑ r, (outcomeProbability model (some r) ρ / acceptanceProbability model ρ) •
        outcomeConditional model (some r) ρ := conditional_barycenter model ρ h

example (model : Readout) (r : BellMeasurement) (ρ : FourState)
    (h : 0 < acceptanceProbability model ρ) :
    0 ≤ outcomeProbability model (some r) ρ / acceptanceProbability model ρ :=
  div_nonneg (outcome_probability_nonnegative model (some r) ρ) (le_of_lt h)

example (model : Readout) (o : Outcome) (ρ : FourState)
    (h : 0 < outcomeProbability model o ρ) :
    (outcomeState model o ρ h).matrix.PosSemidef ∧
    (outcomeState model o ρ h).matrix.trace = 1 :=
  ⟨(outcomeState model o ρ h).positive, (outcomeState model o ρ h).trace_one⟩
