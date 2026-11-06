import Verification.QuantumCascadedSwapping

noncomputable section
open QuantumCascadedSwapping QuantumCorrelatedMemoryBSM
open QuantumBellDiagonalInputs QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumOutcomeInstrument QuantumNullConditioning
open scoped BigOperators ComplexOrder Matrix Kronecker

-- Distinct environment dimensions: a 4-by-32 composite with fresh three-level memory.
example (C : Cascade (Fin 2) (Fin 3) Unit (Fin 2)) (o : TerminalOutcome)
    (M : Matrix ((FourIndex × Fin 2) × Fin 5) ((FourIndex × Fin 2) × Fin 5) ℂ)
    (hM : M.PosSemidef) :
    (liftMapGen (Fin 5) (terminalBranch C o).map M).PosSemidef :=
  terminal_cp C o (Fin 5) M hM

-- Complex linearity is on unnormalized matrices; no PSD restriction here.
example (C : Cascade (Fin 2) (Fin 3) Unit (Fin 2)) (o : TerminalOutcome)
    (M N : JointFourDensity (Fin 2)) :
    (terminalBranch C o).map (M + Complex.I • N) =
      (terminalBranch C o).map M + Complex.I • (terminalBranch C o).map N := by
  exact (terminalBranch C o).linear.map_add M (Complex.I • N) |>.trans
    (congrArg ((terminalBranch C o).map M + ·)
      ((terminalBranch C o).linear.map_smul Complex.I N))

example : Fintype.card TerminalOutcome = 21 := terminal_outcome_card

-- All second branches form a normalized conditional distribution when first probability > 0.
example (C : Cascade (Fin 2) (Fin 3) Unit (Fin 2)) (r : BellMeasurement)
    (N : JointFourDensity (Fin 2)) (hN : N.PosSemidef)
    (hp : 0 < ((C.first.branch (some r)).map N).trace.re) :
    (∑ o : Outcome, (conditionalContinuation C r o N).trace) = 1 :=
  conditional_total_trace C r N hN hp

-- The real chain rule applies to PSD inputs and is not division of the same probability.
example (C : Cascade (Fin 2) (Fin 3) Unit (Fin 2)) (r : BellMeasurement) (o : Outcome)
    (N : JointFourDensity (Fin 2)) (hN : N.PosSemidef) :
    ((cascadeBranch C r o).map N).trace.re =
      ((C.first.branch (some r)).map N).trace.re *
        (conditionalContinuation C r o N).trace.re :=
  cascade_probability_factorization C r o N hN
