import Verification.QuantumStateAvailabilityContract

open QuantumStateAvailabilityContract
open scoped BigOperators
noncomputable section

private def ket0 : QubitState := (1, 0)
private def ket1 : QubitState := (0, 1)
private def complexKet : QubitState := (3 / 5, (4 / 5) * Complex.I)

example : Normalized ket0 := by norm_num [Normalized, qubitNormSq, ket0]
example : Normalized ket1 := by norm_num [Normalized, qubitNormSq, ket1]
example : Normalized complexKet := by
  norm_num [Normalized, qubitNormSq, complexKet, Complex.normSq_mul]
example : ¬ Normalized ((2, 0) : QubitState) := by norm_num [Normalized, qubitNormSq]
example : bellKet .psiMinus 0 1 = bellCoeff := by simp [bellKet]
example : bellKet .psiMinus 1 0 = -bellCoeff := by simp [bellKet]
example : bellKet .psiMinus 0 0 = 0 := by simp [bellKet]
example : (∑ i, ∑ j, star (bellKet .phiPlus i j) * bellKet .phiMinus i j) = 0 := by
  simpa using bell_orthonormal .phiPlus .phiMinus
example : (∑ i, ∑ j, star (bellKet .psiMinus i j) * bellKet .psiMinus i j) = 1 := by
  simpa using bell_orthonormal .psiMinus .psiMinus
example : bobBranch .psiMinus complexKet = (-(4 / 5) * Complex.I, 3 / 5) := by
  simp [bobBranch, complexKet]
example : applyCorrection .psiMinus (bobBranch .psiMinus complexKet) = complexKet :=
  teleportation_exact_recovery _ _
example : applyCorrection .phiMinus (bobBranch .phiMinus complexKet) = complexKet :=
  teleportation_exact_recovery _ _
example : applyCorrection .psiPlus (bobBranch .psiPlus complexKet) = complexKet :=
  teleportation_exact_recovery _ _
example : applyCorrection .phiPlus (bobBranch .phiPlus complexKet) = complexKet :=
  teleportation_exact_recovery _ _
-- XZ is not the exact inverse of XZ: the global minus sign matters for vector equality.
example : bobBranch .psiMinus (bobBranch .psiMinus ket0) = (-1, 0) := by
  simp [bobBranch, ket0]
example : bobBranch .psiMinus (bobBranch .psiMinus ket0) ≠ ket0 := by
  norm_num [bobBranch, ket0]
example : qubitDensity ((-1, 0) : QubitState) = qubitDensity ket0 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [qubitDensity, amp, ket0]
example : bellContraction .psiMinus (initialState ket0) 1 = 1 / 2 := by
  rw [bell_contraction_formula]
  simp [amp, bobBranch, ket0]
example : bellContraction .psiMinus (initialState ket1) 0 = -1 / 2 := by
  rw [bell_contraction_formula]
  norm_num [amp, bobBranch, ket1]
example : bellProject .psiMinus (initialState ket0) 0 1 1 = bellCoeff * (1 / 2) := by
  simp [bellProject, bell_contraction_formula, bellKet, amp, bobBranch, ket0]
example (ψ : QubitState) : initialState ψ = bellProject .phiPlus (initialState ψ) +
    bellProject .phiMinus (initialState ψ) + bellProject .psiPlus (initialState ψ) +
    bellProject .psiMinus (initialState ψ) := canonical_bell_decomposition ψ
example (m : BellMeasurement) : outcomeProbability m complexKet = 1 / 4 := by
  apply outcome_probability_quarter
  norm_num [Normalized, qubitNormSq, complexKet, Complex.normSq_mul]
example (m : BellMeasurement) : outcomeProbability m ((2, 0) : QubitState) = 1 := by
  rw [outcome_probability_scaling]
  norm_num [qubitNormSq]
example (m : BellMeasurement) : outcomeProbability m ((0, 0) : QubitState) = 0 := by
  rw [outcome_probability_scaling]
  norm_num [qubitNormSq]
example (m : BellMeasurement) : normSq3 (normalizedPost m ((2, 0) : QubitState)) = 4 := by
  rw [normalized_post_norm]
  norm_num [qubitNormSq]
example (m : BellMeasurement) : senderReduced (normalizedPost m complexKet) = mixedHalf := by
  apply no_cloning_collapse
  norm_num [Normalized, qubitNormSq, complexKet, Complex.normSq_mul]
example (m : BellMeasurement) :
    senderReduced (normalizedPost m ((2, 0) : QubitState)) 0 0 = 2 := by
  rw [sender_reduced_scaling]
  norm_num [qubitNormSq, mixedHalf]
example : unconditionedBob ket0 = mixedHalf := by
  apply classical_channel_requirement
  norm_num [Normalized, qubitNormSq, ket0]
example : unconditionedBob complexKet 0 1 = 0 := by
  rw [classical_channel_requirement complexKet
    (by norm_num [Normalized, qubitNormSq, complexKet, Complex.normSq_mul])]
  simp [mixedHalf]
example : unconditionedBob ((2, 0) : QubitState) 0 0 = 8 := by
  norm_num [unconditionedBob, outcome_probability_scaling, bob_reduced_post,
    qubitDensity, bobBranch, amp, qubitNormSq]
example : ¬ ∃ f : QubitState → QubitState, ∀ m ψ, f (bobBranch m ψ) = ψ :=
  no_branch_oblivious_decoder
example (m : BellMeasurement) (c : ℂ) (ψ : QubitState) :
    applyCorrection m (c • ψ) = c • applyCorrection m ψ := correction_smul _ _ _
example (m : BellMeasurement) (ψ : QubitState) :
    (correctionLinearEquiv m).symm ((correctionLinearEquiv m) ψ) = ψ :=
  (correctionLinearEquiv m).symm_apply_apply ψ
example : qsaTransition ⟨false, some .phiPlus⟩ ket0 = none := rfl
example : qsaTransition ⟨true, none⟩ ket0 = none := rfl
example : qsaTransition ⟨true, some .psiMinus⟩ (bobBranch .psiMinus complexKet) =
    some complexKet := qsa_exact_output _ _ _ rfl rfl
-- A supplied but wrong report passes the policy and can yield the wrong state.
example : qsaTransition ⟨true, some .psiPlus⟩ (bobBranch .phiPlus ket0) = some ket1 := rfl
example : qsaTransition ⟨true, some .psiPlus⟩ (bobBranch .phiPlus ket0) ≠ some ket0 := by
  norm_num [qsaTransition, applyCorrection, bobBranch, ket0]
-- A wrong phase label happens to fix this particular input: correctness is not an iff.
example : qsaTransition ⟨true, some .phiMinus⟩ (bobBranch .phiPlus ket0) = some ket0 := by
  simp [qsaTransition, applyCorrection, bobBranch, ket0]
example (ψ : QubitState) : decodeNV (encodeNV ψ) = ψ := nv_logical_roundtrip ψ
example : encodeNV complexKet = (3 / 5, 0, (4 / 5) * Complex.I) := rfl
example (m : BellMeasurement) (ψ : QubitState) :
    legacyState (bobBranch m ψ) =
      QuantumTeleportationProtocol.bobReceivedState (legacyOutcome m) (legacyState ψ) :=
  legacy_branch_adapter _ _
-- The resource is specifically Phi+, not an arbitrary entangled pair.
example : bellContraction .phiPlus
    (fun i j k => amp ((1, 1) : QubitState) i * bellKet .phiMinus j k) 1 = -1 / 2 := by
  simp [bellContraction, bellKet, amp, Fin.sum_univ_two]
  ring_nf
  norm_num [bellCoeff_sq]
example : QuantumStateAvailabilitySuite := verification_suite
