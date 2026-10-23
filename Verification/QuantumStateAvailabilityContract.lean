/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumDiamondNVInterfaceContract
import Verification.QuantumTeleportationProtocol
import Verification.QuantumNoCloningUnitary
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Ideal Bell projection and quantum state availability

The input is an arbitrary complex amplitude pair; normalization is explicit.
Born weights are derived from projections of a three-qubit state. Partial traces
are actual finite sums. The scalar norm is the Hilbert sum, not the product sup norm.
There is no physical NV implementation, message authentication or timing claim.
-/
namespace QuantumStateAvailabilityContract

noncomputable section
open scoped BigOperators

abbrev QubitState := ℂ × ℂ
abbrev PairKet := Fin 2 → Fin 2 → ℂ
abbrev TripleKet := Fin 2 → Fin 2 → Fin 2 → ℂ
abbrev Density := Fin 2 → Fin 2 → ℂ

def qubitNormSq (ψ : QubitState) : ℝ := Complex.normSq ψ.1 + Complex.normSq ψ.2
def Normalized (ψ : QubitState) : Prop := qubitNormSq ψ = 1
def amp (ψ : QubitState) (i : Fin 2) : ℂ := if i = 0 then ψ.1 else ψ.2

inductive BellMeasurement
  | phiPlus | phiMinus | psiPlus | psiMinus
  deriving DecidableEq, Repr

def bellScale : ℝ := 1 / Real.sqrt 2
def bellCoeff : ℂ := (bellScale : ℂ)

theorem bellScale_mul_self : bellScale * bellScale = 1 / 2 := by
  rw [bellScale, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem bellCoeff_sq : bellCoeff ^ 2 = (1 / 2 : ℂ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) bellScale_mul_self
  simpa [bellCoeff, pow_two] using h

@[simp] theorem bellCoeff_conj : (starRingEnd ℂ) bellCoeff = bellCoeff := by simp [bellCoeff]
@[simp] theorem bellCoeff_normSq : Complex.normSq bellCoeff = 1 / 2 := by
  simpa [bellCoeff, Complex.normSq_ofReal] using bellScale_mul_self

def bellKet (m : BellMeasurement) : PairKet := fun i j =>
  match m with
  | .phiPlus => if i = j then bellCoeff else 0
  | .phiMinus => if i = j then if i = 0 then bellCoeff else -bellCoeff else 0
  | .psiPlus => if i ≠ j then bellCoeff else 0
  | .psiMinus => if i ≠ j then if i = 0 then bellCoeff else -bellCoeff else 0

def bobBranch (m : BellMeasurement) (ψ : QubitState) : QubitState :=
  match m with
  | .phiPlus => ψ
  | .phiMinus => (ψ.1, -ψ.2)
  | .psiPlus => (ψ.2, ψ.1)
  | .psiMinus => (-ψ.2, ψ.1)

def applyCorrection (m : BellMeasurement) (ψ : QubitState) : QubitState :=
  match m with
  | .phiPlus => ψ
  | .phiMinus => (ψ.1, -ψ.2)
  | .psiPlus => (ψ.2, ψ.1)
  | .psiMinus => (ψ.2, -ψ.1)

def tensorBellQubit (b : PairKet) (ψ : QubitState) : TripleKet :=
  fun i j k => b i j * amp ψ k

def initialState (ψ : QubitState) : TripleKet :=
  fun i j k => amp ψ i * bellKet .phiPlus j k

def bellContraction (m : BellMeasurement) (v : TripleKet) (k : Fin 2) : ℂ :=
  ∑ i, ∑ j, star (bellKet m i j) * v i j k

def bellProject (m : BellMeasurement) (v : TripleKet) : TripleKet :=
  fun i j k => bellKet m i j * bellContraction m v k

def normalizedPost (m : BellMeasurement) (ψ : QubitState) : TripleKet :=
  tensorBellQubit (bellKet m) (bobBranch m ψ)

theorem bell_contraction_formula (m : BellMeasurement) (ψ : QubitState) (k : Fin 2) :
    bellContraction m (initialState ψ) k = (1 / 2 : ℂ) * amp (bobBranch m ψ) k := by
  cases m <;> fin_cases k <;>
    simp [bellContraction, initialState, bellKet, amp, bobBranch, Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [bellCoeff_sq] <;> ring

theorem bell_orthonormal (m l : BellMeasurement) :
    (∑ i, ∑ j, star (bellKet m i j) * bellKet l i j) = if m = l then 1 else 0 := by
  cases m <;> cases l <;> simp [bellKet, Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [bellCoeff_sq]

theorem bell_projection_formula (m : BellMeasurement) (ψ : QubitState) :
    bellProject m (initialState ψ) = (1 / 2 : ℂ) • normalizedPost m ψ := by
  funext i j k
  simp only [bellProject, bell_contraction_formula, normalizedPost, tensorBellQubit,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem canonical_bell_decomposition (ψ : QubitState) :
    initialState ψ = bellProject .phiPlus (initialState ψ) +
      bellProject .phiMinus (initialState ψ) + bellProject .psiPlus (initialState ψ) +
      bellProject .psiMinus (initialState ψ) := by
  simp only [bell_projection_formula]
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [initialState, normalizedPost, tensorBellQubit, bellKet, amp, bobBranch] <;> ring

def normSq3 (v : TripleKet) : ℝ := ∑ i, ∑ j, ∑ k, Complex.normSq (v i j k)
def outcomeProbability (m : BellMeasurement) (ψ : QubitState) : ℝ :=
  normSq3 (bellProject m (initialState ψ))

theorem initial_state_norm (ψ : QubitState) : normSq3 (initialState ψ) = qubitNormSq ψ := by
  simp [normSq3, initialState, amp, bellKet, Fin.sum_univ_two,
    Complex.normSq_mul, qubitNormSq]
  ring

theorem actual_post_normalization (m : BellMeasurement) (ψ : QubitState) :
    (2 : ℂ) • bellProject m (initialState ψ) = normalizedPost m ψ := by
  rw [bell_projection_formula, smul_smul]
  norm_num

theorem bob_branch_norm (m : BellMeasurement) (ψ : QubitState) :
    qubitNormSq (bobBranch m ψ) = qubitNormSq ψ := by
  cases m <;> simp [qubitNormSq, bobBranch, add_comm]

theorem normalized_post_norm (m : BellMeasurement) (ψ : QubitState) :
    normSq3 (normalizedPost m ψ) = qubitNormSq ψ := by
  cases m <;>
    simp [normSq3, normalizedPost, tensorBellQubit, bellKet, amp, bobBranch,
      Fin.sum_univ_two, Complex.normSq_mul, qubitNormSq] <;> ring

theorem outcome_probability_scaling (m : BellMeasurement) (ψ : QubitState) :
    outcomeProbability m ψ = qubitNormSq ψ / 4 := by
  rw [outcomeProbability, bell_projection_formula]
  cases m <;>
    norm_num [normSq3, normalizedPost, tensorBellQubit, bellKet, amp, bobBranch,
      Fin.sum_univ_two, Complex.normSq_mul, qubitNormSq] <;> ring

theorem outcome_probability_quarter (m : BellMeasurement) (ψ : QubitState)
    (hψ : Normalized ψ) : outcomeProbability m ψ = 1 / 4 := by
  rw [outcome_probability_scaling, hψ]

theorem outcome_probabilities_sum (ψ : QubitState) (hψ : Normalized ψ) :
    outcomeProbability .phiPlus ψ + outcomeProbability .phiMinus ψ +
      outcomeProbability .psiPlus ψ + outcomeProbability .psiMinus ψ = 1 := by
  simp only [outcome_probability_quarter _ _ hψ]
  norm_num

theorem teleportation_exact_recovery (m : BellMeasurement) (ψ : QubitState) :
    applyCorrection m (bobBranch m ψ) = ψ := by
  cases m <;> simp [applyCorrection, bobBranch]

theorem correction_right_inverse (m : BellMeasurement) (ψ : QubitState) :
    bobBranch m (applyCorrection m ψ) = ψ := by
  cases m <;> simp [applyCorrection, bobBranch]

theorem correction_add (m : BellMeasurement) (ψ φ : QubitState) :
    applyCorrection m (ψ + φ) = applyCorrection m ψ + applyCorrection m φ := by
  cases m <;> apply Prod.ext <;> simp [applyCorrection] <;> ring

theorem correction_smul (m : BellMeasurement) (c : ℂ) (ψ : QubitState) :
    applyCorrection m (c • ψ) = c • applyCorrection m ψ := by
  cases m <;> apply Prod.ext <;> simp [applyCorrection]

theorem teleportation_isometry (m : BellMeasurement) (ψ : QubitState) :
    qubitNormSq (applyCorrection m ψ) = qubitNormSq ψ := by
  cases m <;> simp [applyCorrection, qubitNormSq, add_comm]

def correctionLinearEquiv (m : BellMeasurement) : QubitState ≃ₗ[ℂ] QubitState where
  toFun := applyCorrection m
  invFun := bobBranch m
  left_inv := correction_right_inverse m
  right_inv := teleportation_exact_recovery m
  map_add' := correction_add m
  map_smul' := correction_smul m

def qubitDensity (ψ : QubitState) : Density := fun i j => amp ψ i * star (amp ψ j)

def senderReduced (v : TripleKet) : Density := fun i j =>
  ∑ b, ∑ c, v i b c * star (v j b c)

def bobReduced (v : TripleKet) : Density := fun i j =>
  ∑ a, ∑ b, v a b i * star (v a b j)

def mixedHalf : Density := fun i j => if i = j then 1 / 2 else 0

theorem sender_reduced_scaling (m : BellMeasurement) (ψ : QubitState) :
    senderReduced (normalizedPost m ψ) = (qubitNormSq ψ : ℂ) • mixedHalf := by
  funext i j
  cases m <;> fin_cases i <;> fin_cases j <;>
    simp [senderReduced, normalizedPost, tensorBellQubit, bellKet, bobBranch, amp,
      mixedHalf, qubitNormSq, Fin.sum_univ_two, map_mul, map_neg,
      Complex.ofReal_add, ← Complex.mul_conj] <;>
    ring_nf <;> norm_num [bellCoeff_sq] <;> ring

/-- Sender-local independence after Bell projection; not the general no-cloning theorem. -/
theorem no_cloning_collapse (m : BellMeasurement) (ψ : QubitState) (hψ : Normalized ψ) :
    senderReduced (normalizedPost m ψ) = mixedHalf := by
  rw [sender_reduced_scaling, hψ]
  simp

theorem bob_reduced_post (m : BellMeasurement) (ψ : QubitState) :
    bobReduced (normalizedPost m ψ) = qubitDensity (bobBranch m ψ) := by
  funext i j
  cases m <;> fin_cases i <;> fin_cases j <;>
    simp [bobReduced, normalizedPost, tensorBellQubit, bellKet, bobBranch, amp,
      qubitDensity, Fin.sum_univ_two, map_mul, map_neg] <;>
    ring_nf <;> norm_num [bellCoeff_sq] <;> ring

def unconditionedBob (ψ : QubitState) : Density :=
  (outcomeProbability .phiPlus ψ : ℂ) • bobReduced (normalizedPost .phiPlus ψ) +
  (outcomeProbability .phiMinus ψ : ℂ) • bobReduced (normalizedPost .phiMinus ψ) +
  (outcomeProbability .psiPlus ψ : ℂ) • bobReduced (normalizedPost .psiPlus ψ) +
  (outcomeProbability .psiMinus ψ : ℂ) • bobReduced (normalizedPost .psiMinus ψ)

theorem bob_unconditioned_mixed (ψ : QubitState) (hψ : Normalized ψ) :
    unconditionedBob ψ = mixedHalf := by
  have hn : (ψ.1 * (starRingEnd ℂ) ψ.1 + ψ.2 * (starRingEnd ℂ) ψ.2 : ℂ) = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hψ
    simpa [Normalized, qubitNormSq, Complex.ofReal_add, ← Complex.mul_conj] using h
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [unconditionedBob, outcome_probability_quarter _ _ hψ, bob_reduced_post,
      qubitDensity, bobBranch, amp, mixedHalf] <;> linear_combination hn / 2

theorem no_branch_oblivious_decoder :
    ¬ ∃ f : QubitState → QubitState, ∀ m ψ, f (bobBranch m ψ) = ψ := by
  rintro ⟨f, hf⟩
  have h0 := hf .phiPlus (1, 0)
  have h1 := hf .psiPlus (0, 1)
  simp only [bobBranch] at h0 h1
  have h := congrArg Prod.fst (h0.symm.trans h1)
  norm_num at h

def legacyOutcome : BellMeasurement → QuantumTeleportationProtocol.BellMeasurement
  | .phiPlus => .phiPlus
  | .phiMinus => .phiMinus
  | .psiPlus => .psiPlus
  | .psiMinus => .psiMinus

def legacyState (ψ : QubitState) : QuantumTeleportationProtocol.QubitState := ⟨ψ.1, ψ.2⟩

theorem legacy_branch_adapter (m : BellMeasurement) (ψ : QubitState) :
    legacyState (bobBranch m ψ) =
      QuantumTeleportationProtocol.bobReceivedState (legacyOutcome m) (legacyState ψ) := by
  cases m <;> rfl

theorem legacy_correction_adapter (m : BellMeasurement) (ψ : QubitState) :
    legacyState (applyCorrection m ψ) = QuantumTeleportationProtocol.appMat
      (QuantumTeleportationProtocol.bobCorrectionOp (legacyOutcome m)) (legacyState ψ) := by
  cases m <;>
    ext <;> simp [legacyState, applyCorrection, legacyOutcome,
      QuantumTeleportationProtocol.appMat, QuantumTeleportationProtocol.bobCorrectionOp,
      QuantumTeleportationProtocol.matI, QuantumTeleportationProtocol.pauliX,
      QuantumTeleportationProtocol.pauliZ, QuantumTeleportationProtocol.pauliZX]

theorem separate_no_universal_cloning :
    ¬ ∃ (U : QuantumNoCloningUnitary.Joint 2) (b : QuantumNoCloningUnitary.Ket 2),
      QuantumNoCloningUnitary.Unitary U ∧ QuantumNoCloningUnitary.Normalized b ∧
      ∀ ψ : QuantumNoCloningUnitary.Ket 2, QuantumNoCloningUnitary.Normalized ψ →
        QuantumNoCloningUnitary.DensityClones U b ψ :=
  QuantumNoCloningUnitary.no_universal_unitary_cloning (by norm_num)

/-- Supplied metadata, not a proof of entanglement or certificate authenticity. -/
structure QSAStatus where
  pairCertified : Bool
  reportedOutcome : Option BellMeasurement

/-- A classical release policy; the payload is actually corrected using the supplied label. -/
def qsaTransition (status : QSAStatus) (received : QubitState) : Option QubitState :=
  if status.pairCertified then
    status.reportedOutcome.map (fun m => applyCorrection m received)
  else none

/-- Availability means an output of this release policy, not a physical availability theorem. -/
theorem qsa_register_availability (status : QSAStatus) (received : QubitState) :
    (qsaTransition status received).isSome = true ↔
      status.pairCertified = true ∧ status.reportedOutcome.isSome = true := by
  rcases status with ⟨certified, reported⟩
  cases certified <;> cases reported <;> simp [qsaTransition]

/-- Correctness needs the reported label to agree with the actual ideal measurement branch. -/
theorem qsa_exact_output (status : QSAStatus) (m : BellMeasurement) (ψ : QubitState)
    (hp : status.pairCertified = true) (hm : status.reportedOutcome = some m) :
    qsaTransition status (bobBranch m ψ) = some ψ := by
  simp [qsaTransition, hp, hm, teleportation_exact_recovery]

theorem qsa_missing_certificate (status : QSAStatus) (received : QubitState)
    (hm : status.reportedOutcome = none) : qsaTransition status received = none := by
  simp [qsaTransition, hm]

theorem qsa_uncertified_pair (status : QSAStatus) (received : QubitState)
    (hp : status.pairCertified = false) : qsaTransition status received = none := by
  simp [qsaTransition, hp]

/-- Logical embedding in the existing ideal NV amplitude model, not a physical memory write. -/
def encodeNV (ψ : QubitState) : QuantumDiamondNVInterfaceContract.CoherentAmp :=
  (ψ.1, 0, ψ.2)

def decodeNV (a : QuantumDiamondNVInterfaceContract.CoherentAmp) : QubitState :=
  (a.1, a.2.2)

theorem nv_logical_roundtrip (ψ : QubitState) : decodeNV (encodeNV ψ) = ψ := rfl

theorem nv_embedding_isometry (ψ : QubitState) :
    QuantumDiamondNVInterfaceContract.ampIntensity (encodeNV ψ) = qubitNormSq ψ := by
  simp [QuantumDiamondNVInterfaceContract.ampIntensity, encodeNV, qubitNormSq]

theorem nv_encoded_recovery (m : BellMeasurement) (ψ : QubitState) :
    encodeNV (applyCorrection m (bobBranch m ψ)) = encodeNV ψ := by
  rw [teleportation_exact_recovery]

theorem classical_channel_requirement (ψ : QubitState) (hψ : Normalized ψ) :
    unconditionedBob ψ = mixedHalf := bob_unconditioned_mixed ψ hψ

structure QuantumStateAvailabilitySuite : Prop where
  projection : ∀ (m : BellMeasurement) (ψ : QubitState),
    bellProject m (initialState ψ) = (1 / 2 : ℂ) • normalizedPost m ψ
  decomposition : ∀ (ψ : QubitState),
    initialState ψ = bellProject .phiPlus (initialState ψ) +
      bellProject .phiMinus (initialState ψ) + bellProject .psiPlus (initialState ψ) +
      bellProject .psiMinus (initialState ψ)
  born_weights : ∀ (m : BellMeasurement) (ψ : QubitState),
    Normalized ψ → outcomeProbability m ψ = 1 / 4
  recovery : ∀ (m : BellMeasurement) (ψ : QubitState), applyCorrection m (bobBranch m ψ) = ψ
  correction_inverse : ∀ (m : BellMeasurement) (ψ : QubitState),
    bobBranch m (applyCorrection m ψ) = ψ
  correction_linear_add : ∀ (m : BellMeasurement) (ψ φ : QubitState),
    applyCorrection m (ψ + φ) = applyCorrection m ψ + applyCorrection m φ
  correction_linear_smul : ∀ (m : BellMeasurement) (c : ℂ) (ψ : QubitState),
    applyCorrection m (c • ψ) = c • applyCorrection m ψ
  isometry : ∀ (m : BellMeasurement) (ψ : QubitState),
    qubitNormSq (applyCorrection m ψ) = qubitNormSq ψ
  sender_local : ∀ (m : BellMeasurement) (ψ : QubitState),
    Normalized ψ → senderReduced (normalizedPost m ψ) = mixedHalf
  classical_requirement : ∀ (ψ : QubitState), Normalized ψ → unconditionedBob ψ = mixedHalf
  no_blind_decoder : ¬ ∃ f : QubitState → QubitState, ∀ m ψ, f (bobBranch m ψ) = ψ
  gate_availability : ∀ (status : QSAStatus) (received : QubitState),
    (qsaTransition status received).isSome = true ↔
      status.pairCertified = true ∧ status.reportedOutcome.isSome = true
  gate_recovery : ∀ (status : QSAStatus) (m : BellMeasurement) (ψ : QubitState),
    status.pairCertified = true → status.reportedOutcome = some m →
    qsaTransition status (bobBranch m ψ) = some ψ
  nv_roundtrip : ∀ (ψ : QubitState), decodeNV (encodeNV ψ) = ψ
  nv_isometry : ∀ (ψ : QubitState),
    QuantumDiamondNVInterfaceContract.ampIntensity (encodeNV ψ) = qubitNormSq ψ
  legacy_branch : ∀ (m : BellMeasurement) (ψ : QubitState), legacyState (bobBranch m ψ) =
    QuantumTeleportationProtocol.bobReceivedState (legacyOutcome m) (legacyState ψ)
  universal_no_cloning :
    ¬ ∃ (U : QuantumNoCloningUnitary.Joint 2) (b : QuantumNoCloningUnitary.Ket 2),
      QuantumNoCloningUnitary.Unitary U ∧ QuantumNoCloningUnitary.Normalized b ∧
      ∀ ψ : QuantumNoCloningUnitary.Ket 2, QuantumNoCloningUnitary.Normalized ψ →
        QuantumNoCloningUnitary.DensityClones U b ψ

theorem verification_suite : QuantumStateAvailabilitySuite := {
  projection := bell_projection_formula
  decomposition := canonical_bell_decomposition
  born_weights := outcome_probability_quarter
  recovery := teleportation_exact_recovery
  correction_inverse := correction_right_inverse
  correction_linear_add := correction_add
  correction_linear_smul := correction_smul
  isometry := teleportation_isometry
  sender_local := no_cloning_collapse
  classical_requirement := classical_channel_requirement
  no_blind_decoder := no_branch_oblivious_decoder
  gate_availability := qsa_register_availability
  gate_recovery := qsa_exact_output
  nv_roundtrip := nv_logical_roundtrip
  nv_isometry := nv_embedding_isometry
  legacy_branch := legacy_branch_adapter
  universal_no_cloning := separate_no_universal_cloning
}

end
end QuantumStateAvailabilityContract
