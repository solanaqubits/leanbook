import Verification.QuantumMemoryCounterexample

noncomputable section
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGeneralBellReadout QuantumSwappingInstrument QuantumOutcomeInstrument
open QuantumGateNoiseComposition QuantumNoiseTransport QuantumOrderedNoiseComposition
open QuantumPersistentEnvironment QuantumMemoryCounterexample
open scoped BigOperators ComplexOrder Matrix

-- Empty circuit and arbitrary finite joint channel; initialization is fixed.
example (M : Qubit) : (persistent ([] : List (Stage (Fin 2 × Fin 2))) 0).map M = M := by
  rw [persistent_map]
  exact trace_environment_prepare _ _

example {κ : Type} [Fintype κ] (E : CPTP (Fin 3 × Fin 2) κ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (reduced E (1 : Fin 2)).map M = traceEnvironment (E.map (prepare 1 M)) := reduced_map E 1 M

example (ss : List (Stage (Fin 3 × Fin 2))) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    ((persistent ss (1 : Fin 2)).map M).trace = M.trace := (persistent ss 1).trace M

example (ss : List (Stage (Fin 3 × Fin 2))) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hM : M.PosSemidef) : ((persistent ss (1 : Fin 2)).map M).PosSemidef :=
  (persistent ss 1).positive M hM

-- Nontrivial ancilla: CPTP is checked through the existing block-map CP theorem.
example (ss : List (Stage (Fin 3 × Fin 2)))
    (R : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) (hR : R.PosSemidef) :
    (Matrix.of fun a b : Fin 2 × Fin 3 =>
      (persistent ss (1 : Fin 2)).map
        (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2).PosSemidef :=
  (persistent ss 1).cp 2 R hR

def idleJoint : Stage (Fin 2 × Fin 2) :=
  ⟨Unit, inferInstance, identityGate _, identityChannel _⟩

example : ReturnsFresh (0 : Fin 2) idleJoint := by
  have h (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      (noisyGate idleJoint.gate idleJoint.noise).map N = N := by
    rw [noisy_gate_map]
    change (identityChannel (Fin 2 × Fin 2)).map (1 * N *
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).conjTranspose) = N
    rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, identity_map]
  intro M
  rw [reduced_map, h, trace_environment_prepare]

example (ss : List (Stage (Fin 2 × Fin 2))) (h : ∀ s ∈ ss, ReturnsFresh (0 : Fin 2) s)
    (M : Qubit) : (persistent ss (0 : Fin 2)).map M = resetRun ss (0 : Fin 2) M :=
  persistent_equals_reset_of_fresh ss 0 h M

-- Memory counterexample uses valid states, not arbitrary unphysical matrices.
example (minus : Bool) : (coherent minus).PosSemidef ∧ (coherent minus).trace = 1 :=
  ⟨coherent_positive minus, coherent_trace minus⟩
example : (persistent [collision] (0 : Fin 2)).map (coherent false) =
    (persistent [collision] (0 : Fin 2)).map (coherent true) := first_marginals_equal
example (M : Qubit) : (persistent [collision,collision] (0 : Fin 2)).map M = M :=
  persistent_twice M
example (M : Qubit) : resetRun [collision,collision] (0 : Fin 2) M = dephase M := reset_twice M
example : ¬ ReturnsFresh (0 : Fin 2) collision := collision_not_fresh
example : ¬ ∃ f : Qubit → Qubit, ∀ M : Qubit, M.PosSemidef → M.trace = 1 →
    f ((persistent [collision] (0 : Fin 2)).map M) =
      (persistent [collision,collision] (0 : Fin 2)).map M := no_system_only_intermediate_map

-- Reuse as a pre-channel of the five-outcome instrument, NOT as internal BSM memory.
example (ss : List (Stage (FourIndex × Fin 2))) (model : Readout) (ρ : FourState) :
    (∑ o : Outcome, noisyOutcome (persistent ss (0 : Fin 2))
      (fun _ => identityChannel PairIndex) model o ρ.matrix).trace = 1 := by
  rw [noisy_total_trace, ρ.trace_one]

example (ss : List (Stage (FourIndex × Fin 2))) (model : Readout) (o : Outcome) :
    IsCP (noisyOutcome (persistent ss (0 : Fin 2))
      (fun _ => identityChannel PairIndex) model o) := noisy_outcome_cp _ _ _ _
