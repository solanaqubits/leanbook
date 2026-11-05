import Verification.QuantumPauliDensityBridge

open scoped ComplexOrder
open QuantumPauliMatrix QuantumPauliDensityBridge
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract

private def zeroNoise : BoundedBps := ⟨0, by decide, by decide⟩
private def fullNoise : BoundedBps := ⟨10000, by decide, by decide⟩
private def oneBps : BoundedBps := ⟨1, by decide, by decide⟩
private def lowFidelity : BoundedBps := ⟨2499, by decide, by decide⟩

-- An actual imaginary phase is required: the product cannot be compressed to a sign.
example : mulPauli4Q xB zB ≠ mulPauli4Q zB xB := by decide
example : (embed (denote4 (mulPauli4Q xB zB))) =
    embed (denote4 xB) * embed (denote4 zB) := pauli_complex_matrix_sound _ _

-- Complex matrix conjugation includes Y components and non-real global phase.
example : embed cnotMatrix * embed (denote2 .imag .y .z) *
    (embed cnotMatrix).conjTranspose =
      embed (denote2 (cnotPhase .imag .y .z) (cnotControl .y .z) (cnotTarget .y .z)) :=
  cnot_complex_conjugation_sound _ _ _

example (p : BoundedBps) : ¬ (p.val < 0 ∨ 10000 < p.val) := by
  have h0 := p.nonneg
  have h1 := p.le_scale
  omega

-- Discrete storage can hide a strict change; the exact numerator retains it.
example : channelNumerator lowFidelity oneBps = 24990001 ∧
    (channelFloor lowFidelity oneBps).val = 2499 := by decide

example (m : BellMeasurement) :
    targetOverlap (depolarize zeroNoise (correctedSwapState m)).matrix = 1 := by
  have h := (born_and_noisy_conditional_fidelity m zeroNoise).2
  simpa [probability, zeroNoise] using h

example (m : BellMeasurement) :
    targetOverlap (depolarize fullNoise (correctedSwapState m)).matrix = (1 / 4 : ℂ) := by
  have h := (born_and_noisy_conditional_fidelity m fullNoise).2
  norm_num [probability, fullNoise] at h ⊢
  exact h

example (m : BellMeasurement) (p : BoundedBps) :
    (depolarize p (correctedSwapState m)).matrix.PosSemidef :=
  (depolarize p (correctedSwapState m)).positive

example (m : BellMeasurement) (p : BoundedBps) :
    (depolarize p (correctedSwapState m)).matrix.trace = 1 :=
  (depolarize p (correctedSwapState m)).trace_one

-- The ideal Born branch weight is distinct from the conditional overlap.
example : swapOutcomeProbability .psiMinus = (1 / 4 : ℝ) :=
  swapping_success_probability _

example (f p : BoundedBps) (ρ : PairState)
    (hf : targetOverlap ρ.matrix = (f.val : ℂ) / 10000) :
    (channelFloor f p).val / (10000 : ℝ) ≤ (targetOverlap (depolarize p ρ).matrix).re ∧
    (targetOverlap (depolarize p ρ).matrix).re < ((channelFloor f p).val + 1) / (10000 : ℝ) :=
  channelFloor_matrix_error f p ρ hf
