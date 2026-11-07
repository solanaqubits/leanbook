import Verification.QuantumScheduledNoisyRepeater
open QuantumScheduledNoisyRepeater QuantumNoisyBBPSSWTree QuantumBBPSSWDistillation
open QuantumCentralDepolarization QuantumEntanglementSwappingPurificationContract
open QuantumNoisyVisibility QuantumBellDiagonalInputs
open scoped ComplexOrder Matrix Kronecker

-- Arbitrary scalar degree checks the actual operator composition, not only a counter.
example (γ : Visibility) (a b : ScheduledState) (c : ℂ) (h : b.matrix = c • a.matrix) :
    ([0, 2, 1].foldl (scheduledStepAcc γ) b).matrix =
      c^64 • ([0, 2, 1].foldl (scheduledStepAcc γ) a).matrix := by
  simpa [scheduledRawPairCount] using scheduledFold_matrix_smul γ [0, 2, 1] a b c h

example (γ w : Visibility) (s : List ℕ) :
    (scheduledRepeaterMatrix γ w s).PosSemidef ∧
    (scheduledRepeaterMatrix γ w s).trace = (scheduledRepeaterProbability γ w s : ℂ) :=
  ⟨scheduledRepeaterMatrix_posSemidef γ w s, scheduledRepeaterMatrix_trace γ w s⟩

example (γ w : Visibility) :
    let D := (scheduledRepeaterProbability γ w [0, 2, 1] : ℂ)⁻¹ •
      scheduledRepeaterMatrix γ w [0, 2, 1]
    D.PosSemidef ∧ D.trace = 1 := scheduledRepeaterMatrix_conditional_density γ w _

example (γ : Visibility) (F : ℝ) (m : ℕ) :
    noisyGeneralTree γ m (werner F) = noisyTreeMatrix γ F m := noisyGeneralTree_werner γ F m
