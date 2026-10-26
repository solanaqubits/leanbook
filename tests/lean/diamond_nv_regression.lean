import Verification.QuantumDiamondNVInterfaceContract

open QuantumDiamondNVInterfaceContract

private def halfPlus : NVSpinPopulation :=
  ⟨1 / 2, 1 / 2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
private def halfMinus : NVSpinPopulation :=
  ⟨1 / 2, 0, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
private def rationalMix : NVSpinPopulation :=
  ⟨9 / 25, 16 / 25, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
private noncomputable def rationalAmp : CoherentAmp := (3 / 5, 4 / 5, 0)
private noncomputable def phaseChangedAmp : CoherentAmp := (-3 / 5, 4 / 5, 0)

example : QuantumDiamondNVInterfaceContract.residual (purePopulation .Zero) = 0
  := by norm_num [QuantumDiamondNVInterfaceContract.residual, purePopulation]
example : QuantumDiamondNVInterfaceContract.residual (purePopulation .Plus) = 1
  := by norm_num [QuantumDiamondNVInterfaceContract.residual, purePopulation]
example : QuantumDiamondNVInterfaceContract.residual (purePopulation .Minus) = 1
  := by norm_num [QuantumDiamondNVInterfaceContract.residual, purePopulation]
example : (opticalPumpStep (1 / 2) (by norm_num) (purePopulation .Plus)).p0 = 1 / 2 ∧
    (opticalPumpStep (1 / 2) (by norm_num) (purePopulation .Plus)).pPlus = 1 / 2 ∧
    (opticalPumpStep (1 / 2) (by norm_num) (purePopulation .Plus)).pMinus = 0 := by
  norm_num [opticalPumpStep, purePopulation]
example : QuantumDiamondNVInterfaceContract.residual (pumpCycles (1 / 2) (by norm_num) 3
  (purePopulation .Plus)) = 1 / 8 := by
  rw [optical_pump_convergence]
  norm_num [QuantumDiamondNVInterfaceContract.residual, purePopulation]
example : (pumpCycles (1 / 2) (by norm_num) 3 (purePopulation .Minus)).p0 = 7 / 8 := by
  rw [optical_pump_p0_exact]
  norm_num [QuantumDiamondNVInterfaceContract.residual, purePopulation]
example (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (p : NVSpinPopulation) : pumpCycles η hη 0 p = p := rfl
example (p : NVSpinPopulation) : opticalPumpStep 0 (by norm_num) p = p := optical_pump_zero _ p
example (k : ℕ) (p : NVSpinPopulation) : pumpCycles 0 (by norm_num) k p = p :=
  pump_cycles_zero_efficiency _ k p
example (p : NVSpinPopulation) : opticalPumpStep 1 (by norm_num) p = purePopulation .Zero :=
  optical_pump_one _ p

-- Pumping is not an invertible preservation of the original population.
example : purePopulation .Plus ≠ purePopulation .Minus ∧
    opticalPumpStep 1 (by norm_num) (purePopulation .Plus) =
      opticalPumpStep 1 (by norm_num) (purePopulation .Minus) := by
  constructor
  · intro h
    have hp := congrArg NVSpinPopulation.pPlus h
    norm_num [purePopulation] at hp
  · rw [optical_pump_one, optical_pump_one]

example (k : ℕ) : 0 < QuantumDiamondNVInterfaceContract.residual (pumpCycles (1 / 2) (by norm_num)
  k (purePopulation .Minus)) :=
  finite_residual_positive (1 / 2) (by norm_num) (by norm_num) k _ (by norm_num
    [QuantumDiamondNVInterfaceContract.residual, purePopulation])
example (k : ℕ) : (pumpCycles (1 / 2) (by norm_num) k (purePopulation .Plus)).p0 < 1 :=
  finite_p0_lt_one (1 / 2) (by norm_num) (by norm_num) k _ (by norm_num
    [QuantumDiamondNVInterfaceContract.residual, purePopulation])
example : ¬ ((0 : ℚ) ≤ 2 ∧ 2 ≤ 1) := by norm_num
example : ((1 - (2 : ℚ)) * 1) < 0 := by norm_num
example : ¬ ((0 : ℚ) ≤ -1 ∧ -1 ≤ 1) := by norm_num
example (p : NVSpinPopulation) :
    Filter.Tendsto (fun k : ℕ => ((pumpCycles (1 / 2) (by norm_num) k p).p0 : ℝ))
      Filter.atTop (nhds 1) := optical_pump_asymptotic_limit _ _ (by norm_num) p

-- Equal p0 does not produce a strict readout increase, even for unequal populations.
example : halfPlus.p0 ≤ halfMinus.p0 ∧
    ¬ luminescenceYield 2 1 halfPlus < luminescenceYield 2 1 halfMinus := by
  norm_num [halfPlus, halfMinus, luminescenceYield]
example : luminescenceYield 2 1 halfPlus = 3 / 2 := by
  norm_num [luminescenceYield, halfPlus]
example : (purePopulation .Plus).p0 < (purePopulation .Zero).p0 ∧
    luminescenceYield 1 1 (purePopulation .Plus) = luminescenceYield 1 1 (purePopulation .Zero)
      := by
  norm_num [luminescenceYield, purePopulation]
example : luminescenceYield (-1) (-2) (purePopulation .Zero) < 0 := by
  norm_num [luminescenceYield, purePopulation]
example : luminescenceYield 2 1 halfPlus < luminescenceYield 2 1 (purePopulation .Zero) :=
  luminescence_contrast_bound _ _ (by norm_num) _ (by norm_num
    [QuantumDiamondNVInterfaceContract.residual, halfPlus])
example (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (p : NVSpinPopulation) :
    luminescenceYield 2 1 p ≤ luminescenceYield 2 1 (opticalPumpStep η hη p) :=
  readout_contrast_monotonicity _ _ (by norm_num) _ _ (optical_pump_p0_monotonicity η hη p)

example : mwPiPulseStep (purePopulation .Zero) = purePopulation .Minus := by
  ext <;> rfl
example : mwPiPulseStep (purePopulation .Plus) = purePopulation .Plus := by
  ext <;> rfl
example (p : NVSpinPopulation) : mwPiPulseStep (mwPiPulseStep p) = p := mw_pi_pulse_involution p
example : luminescenceYield 2 1 (mwPiPulseStep (purePopulation .Minus)) >
    luminescenceYield 2 1 (purePopulation .Minus) := by
  norm_num [luminescenceYield, mwPiPulseStep, purePopulation]

example : coherentPi (1, 0, 0) = (0, 0, -Complex.I) := by norm_num [coherentPi]
example : coherentPi (0, 1, 0) = ((0, 1, 0) : CoherentAmp) := by norm_num [coherentPi]
example (a : CoherentAmp) : coherentPiInverse (coherentPi a) = a := coherent_pi_inverse_left a
example (a : CoherentAmp) : coherentPi (coherentPiInverse a) = a := coherent_pi_inverse_right a
example (a : CoherentAmp) : coherentPi (Complex.I • a) = Complex.I • coherentPi a :=
  coherent_pi_smul Complex.I a
example (a b : CoherentAmp) : ampIntensity (coherentPi a - coherentPi b) = ampIntensity (a - b) :=
  coherent_pi_difference_intensity a b

-- Two normalized amplitudes have the same rational populations but different relative phases.
example : Represents rationalAmp rationalMix := by
  norm_num [Represents, rationalAmp, rationalMix, Complex.normSq_apply]
example : Represents phaseChangedAmp rationalMix := by
  norm_num [Represents, phaseChangedAmp, rationalMix, Complex.normSq_apply]
example : ampIntensity rationalAmp = 1 := by
  norm_num [ampIntensity, rationalAmp, Complex.normSq_apply]
example : rationalAmp ≠ phaseChangedAmp := by
  intro h
  have hr := congrArg (fun a : CoherentAmp => a.1.re) h
  norm_num [rationalAmp, phaseChangedAmp] at hr
example : Represents (coherentPi rationalAmp) (mwPiPulseStep rationalMix) := by
  apply coherent_pi_population_bridge
  norm_num [Represents, rationalAmp, rationalMix, Complex.normSq_apply]
example : coherentPi (coherentPi rationalAmp) = phaseChangedAmp := by
  rw [coherent_pi_twice]
  norm_num [rationalAmp, phaseChangedAmp]

-- The double pi action is not a common global phase on the full three-mode space.
example : ¬ ∃ c : ℂ, coherentPi (coherentPi rationalAmp) = c • rationalAmp := by
  rintro ⟨c, h⟩
  rw [coherent_pi_twice] at h
  have h0 := congrArg (fun a : CoherentAmp => a.1.re) h
  have hp := congrArg (fun a : CoherentAmp => a.2.1.re) h
  norm_num [rationalAmp, Complex.mul_re] at h0 hp
  linarith
