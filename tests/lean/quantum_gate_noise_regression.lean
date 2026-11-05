import Verification.QuantumNoisyVisibility

noncomputable section

open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGeneralBellReadout (Readout)
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoisyVisibility
open scoped BigOperators ComplexOrder Matrix

-- Matrix refinement, including the scalar Kraus weight, has no separability premise.
example {κ ι : Type} [Fintype κ] [Fintype ι] (pre : CPTP FourIndex κ)
    (post : BellMeasurement → CPTP PairIndex ι) (model : Readout) (m r : BellMeasurement)
    (M : FourDensity) : noisyMicro pre post model m r M =
      familyMap (compositeKraus pre post model m r) M := noisy_micro_kraus pre post model m r M

example {κ ι : Type} [Fintype κ] [Fintype ι] (pre : CPTP FourIndex κ)
    (post : BellMeasurement → CPTP PairIndex ι) (model : Readout) (o : Outcome)
    (R : Matrix (Fin 2 × FourIndex) (Fin 2 × FourIndex) ℂ) (hR : R.PosSemidef) :
    (liftMap 2 (noisyOutcome pre post model o) R).PosSemidef :=
  noisy_outcome_cp pre post model o 2 R hR

example {κ ι : Type} [Fintype κ] [Fintype ι] (pre : CPTP FourIndex κ)
    (post : BellMeasurement → CPTP PairIndex ι) (model : Readout) (ρ : FourState) :
    (∑ o : Outcome, noisyOutcome pre post model o ρ.matrix).trace = 1 := by
  rw [noisy_total_trace, ρ.trace_one]

-- Rejection receives pre-noise, but no correction chosen from a nonexistent message.
example {κ ι : Type} [Fintype κ] [Fintype ι] (pre : CPTP FourIndex κ)
    (post : BellMeasurement → CPTP PairIndex ι) (model : Readout) (ρ : FourState) :
    (noisyOutcome pre post model none ρ.matrix).trace.re =
      outcomeProbability model none (noiseState pre ρ) := noisy_probability pre post model none ρ

-- A fixed physical pre-error opens a zero Born branch even with perfect readout.
example : bornProbability .psiPlus ghzState = 0 ∧
    bornProbability .psiPlus (noiseState flipCentralC ghzState) = 1 / 2 := pre_flip_opens_ghz_branch

-- The post channel can improve fidelity without changing trace.
example : targetOverlap (repairingPost.map (QuantumNoisyBellInstrument.bellProjector .psiPlus)) >
    targetOverlap (QuantumNoisyBellInstrument.bellProjector .psiPlus) := by
  rw [cptp_can_increase_target_fidelity.1, cptp_can_increase_target_fidelity.2]
  norm_num

def one : Visibility := ⟨1, by norm_num, by norm_num⟩
def zero : Visibility := ⟨0, by norm_num, by norm_num⟩
def half : Visibility := ⟨1 / 2, by norm_num, by norm_num⟩

example : targetOverlap (noisyWernerOutput half half half half) = (19 / 64 : ℂ) := by
  rw [noisy_visibility_fidelity]
  norm_num [half]

example : targetOverlap (noisyWernerOutput one one half half) = (7 / 16 : ℂ) := by
  rw [noisy_visibility_fidelity]
  norm_num [one, half]

example : targetOverlap (noisyWernerOutput one one one one) = 1 := by
  rw [noisy_visibility_fidelity]
  norm_num [one]

example (bsm corr w v : Visibility) :
    targetOverlap (noisyWernerOutput zero corr w v) = (1 / 4 : ℂ) ∧
    targetOverlap (noisyWernerOutput bsm zero w v) = (1 / 4 : ℂ) := by
  constructor <;> rw [noisy_visibility_fidelity] <;> norm_num [zero]

example : ¬ ∃ v : Visibility, v.val = 2 := by
  rintro ⟨v,h⟩
  have := v.le_one
  linarith

-- At positive input trace, the concrete noisy Werner output is already normalized.
example (bsm corr w v : Visibility) :
    QuantumNullConditioning.normalizeOrZero (noisyWernerOutput bsm corr w v) =
      noisyWernerOutput bsm corr w v := by
  simp [QuantumNullConditioning.normalizeOrZero, noisy_visibility_trace]

example (model : Readout) (o : Outcome) (M : FourDensity) :
    noisyOutcome (identityChannel FourIndex) (fun _ => identityChannel PairIndex) model o M =
      outcomeMap model o M := ideal_noise_refinement model o M
