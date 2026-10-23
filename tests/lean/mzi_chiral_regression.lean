import Verification.PhotonicsMachZehnderChiralContract

open PhotonicsMachZehnderChiralContract
noncomputable section

example (v : Amp2) : chiralMirror (chiralMirror v) = v := chiralMirror_involution v
example (φ : ℝ) (v : Amp2) : intensity (mziStep φ v) = intensity v :=
  mzi_passive_energy_conservation φ v
example (φ : ℝ) :
    intensity (mziStep φ (2 + Complex.I, 3 - Complex.I)) =
      intensity (2 + Complex.I, 3 - Complex.I) := mzi_passive_energy_conservation φ _
example (φ : ℝ) : mziStep φ (0 : Amp2) = 0 := by
  simpa using mzi_smul φ 0 (0 : Amp2)
example (φ : ℝ) (u v : Amp2) :
    mziStep φ (u + v) = mziStep φ u + mziStep φ v := mzi_add φ u v
example (φ : ℝ) (v : Amp2) :
    mziStep φ (Complex.I • v) = Complex.I • mziStep φ v := mzi_smul φ Complex.I v
example (φ : ℝ) (u v : Amp2) :
    intensity (mziStep φ u - mziStep φ v) = intensity (u - v) :=
  mzi_difference_intensity φ u v
example (φ : ℝ) (v : Amp2) : mziStep (-φ) (mziStep φ v) = v := mzi_inverse φ v
example (φ : ℝ) (v : Amp2) : mziStep φ (mziStep (-φ) v) = v := mzi_inverse_right φ v
example (φ ψ : ℝ) (v : Amp2) : mziStep φ (mziStep ψ v) = mziStep (φ + ψ) v :=
  mzi_comp φ ψ v
example (v : Amp2) : beamSplitter (chiralMirror (beamSplitter v)) = (v.2, v.1) :=
  mirror_between_splitters v
example (v : Amp2) : phaseShift Real.pi v = -chiralMirror v := phaseShift_pi v
example (v : Amp2) : mziStep 0 v = v := mzi_zero v
example (v : Amp2) : mziStep Real.pi v = (-v.2, -v.1) := mzi_pi v

-- A negative amplitude is not literally the positive swapped amplitude.
example : mziStep Real.pi (1, 0) ≠ ((0, 1) : Amp2) := by
  rw [mzi_pi]
  norm_num

example : Complex.normSq (mziStep (Real.pi / 2) (1, 0)).1 = 1 / 2 ∧
    Complex.normSq (mziStep (Real.pi / 2) (1, 0)).2 = 1 / 2 := by
  rw [mzi_routing_first, mzi_routing_second]
  norm_num

example (φ : ℝ) :
    Complex.normSq (mziStep φ (1, 0)).1 = Real.cos (φ / 2) ^ 2 ∧
    Complex.normSq (mziStep φ (1, 0)).2 = Real.sin (φ / 2) ^ 2 := mzi_routing_half_angles φ

-- Balanced splitting does not imply equal outputs for arbitrary coherent input.
example : Complex.normSq (beamSplitter (1, 1)).1 = 2 ∧
    Complex.normSq (beamSplitter (1, 1)).2 = 0 := by
  norm_num [beamSplitter, Complex.normSq_mul, bsCoeff, Complex.normSq_ofReal,
    bsScale_mul_self]

-- Omitting 1/sqrt(2) doubles the intensity even on a single occupied port.
example : intensity ((1 : ℂ) + 0, (1 : ℂ) - 0) = 2 ∧ intensity (1, 0) = 1 := by
  norm_num [intensity]

end
