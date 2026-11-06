import Verification.QuantumAdaptiveWernerCascade
open QuantumAdaptiveWernerCascade QuantumWernerCascade QuantumCascadedSwapping
open QuantumCentralDepolarization QuantumNoisyVisibility QuantumMixedEnvironment
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs
open scoped BigOperators ComplexOrder Matrix Kronecker
example (b c w v : Visibility) (s : Schedule) (η : Efficiency)
    (σ : EnvironmentState (Fin 2)) (τ : BellMeasurement → EnvironmentState (Fin 3)) :
    acceptedCascade (adaptiveCascade b c s η (fun _ => closedEfficiency) τ)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ.matrix) = 0 :=
  adaptive_success_zero b c w v s η _ σ τ (closed_second_probability η)
example (b c w v : Visibility) (s : Schedule)
    (σ : EnvironmentState (Fin 2)) (τ : BellMeasurement → EnvironmentState (Fin 3)) :
    (acceptedCascade (adaptiveCascade b c s perfectEfficiency
      (fun _ => perfectEfficiency) τ)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ.matrix)).trace = 1 := by
  rw [adaptive_success_trace, perfect_total_probability]
  norm_num
