import Verification.QuantumBBPSSWDistillation
open QuantumBBPSSWDistillation QuantumCliffordTwirl QuantumRectangularSwapping
open QuantumEntanglementSwappingPurificationContract QuantumCorrelatedMemoryBSM
open scoped ComplexOrder Matrix Kronecker
example (M : FourDensity) : (purified M).trace + (rejected.map M).trace = M.trace :=
  purified_trace_balance M
example : IsCPMap purified := purified_cp
example : ((successProbability 0 : ℂ)⁻¹ • purified (werner 0 ⊗ₖ werner 0)).PosSemidef :=
  purified_conditional_positive 0 (by norm_num)
example : (successProbability (3 / 4) : ℂ)⁻¹ •
    purified (werner (3 / 4) ⊗ₖ werner (3 / 4)) = werner (41 / 52) := by
  rw [purified_conditional]
  norm_num [recurrence, targetMass, successProbability]
example (M : PairDensity) : (twirl M).trace = M.trace := twirl_trace M
example (M : PairDensity) : targetOverlap (twirl M) = targetOverlap M := twirl_overlap M
example (M : PairDensity) :
    twirl M = targetOverlap M • QuantumNoisyBellInstrument.bellProjector .phiPlus +
      ((M.trace-targetOverlap M)/3) •
        (1-QuantumNoisyBellInstrument.bellProjector .phiPlus) := twirl_isotropic_formula M
