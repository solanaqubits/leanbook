/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# Ideal two-mode Hadamard interferometer

Intensity is the sum of squared complex amplitudes, not the product sup norm.
The phase acts on the first arm. At π the exact amplitude map is minus swap.
The name `chiralMirror` denotes a stipulated sign flip; no material chirality,
control-energy cost, apparatus realization or physical dissipation is inferred.
-/
namespace PhotonicsMachZehnderChiralContract

noncomputable section

abbrev Amp2 := ℂ × ℂ

def intensity (v : Amp2) : ℝ := Complex.normSq v.1 + Complex.normSq v.2
def chiralMirror (v : Amp2) : Amp2 := (v.1, -v.2)
def phaseFactor (φ : ℝ) : ℂ := Complex.exp (Complex.I * (φ : ℂ))
def phaseShift (φ : ℝ) (v : Amp2) : Amp2 := (phaseFactor φ * v.1, v.2)
def bsScale : ℝ := 1 / Real.sqrt 2
def bsCoeff : ℂ := (bsScale : ℂ)
def beamSplitter (v : Amp2) : Amp2 :=
  (bsCoeff * (v.1 + v.2), bsCoeff * (v.1 - v.2))
def mziStep (φ : ℝ) (v : Amp2) : Amp2 :=
  beamSplitter (phaseShift φ (beamSplitter v))

theorem bsScale_mul_self : bsScale * bsScale = 1 / 2 := by
  rw [bsScale, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem bsCoeff_sq : bsCoeff ^ 2 = (1 / 2 : ℂ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) bsScale_mul_self
  simpa [bsCoeff, pow_two] using h

@[simp] theorem phaseFactor_re (φ : ℝ) : (phaseFactor φ).re = Real.cos φ := by
  simpa only [phaseFactor, mul_comm Complex.I] using Complex.exp_ofReal_mul_I_re φ

@[simp] theorem phaseFactor_normSq (φ : ℝ) : Complex.normSq (phaseFactor φ) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [phaseFactor, Complex.norm_exp_I_mul_ofReal]

@[simp] theorem phaseFactor_zero : phaseFactor 0 = 1 := by simp [phaseFactor]
@[simp] theorem phaseFactor_pi : phaseFactor Real.pi = -1 := by
  simpa only [phaseFactor, mul_comm Complex.I] using Complex.exp_pi_mul_I

theorem phaseFactor_add (φ ψ : ℝ) : phaseFactor (φ + ψ) = phaseFactor φ * phaseFactor ψ := by
  simp [phaseFactor, mul_add, Complex.exp_add]

theorem chiralMirror_involution (v : Amp2) : chiralMirror (chiralMirror v) = v := by
  simp [chiralMirror]

theorem chiralMirror_preserves_intensity (v : Amp2) :
    intensity (chiralMirror v) = intensity v := by simp [intensity, chiralMirror]

theorem phaseShift_preserves_intensity (φ : ℝ) (v : Amp2) :
    intensity (phaseShift φ v) = intensity v := by
  simp [intensity, phaseShift, Complex.normSq_mul]

theorem beamSplitter_involution (v : Amp2) : beamSplitter (beamSplitter v) = v := by
  apply Prod.ext <;> dsimp [beamSplitter] <;> ring_nf <;> norm_num [bsCoeff_sq] <;> ring

/-- Inserting the stipulated sign flip between Hadamard splitters swaps amplitudes. -/
theorem mirror_between_splitters (v : Amp2) :
    beamSplitter (chiralMirror (beamSplitter v)) = (v.2, v.1) := by
  apply Prod.ext <;> dsimp [beamSplitter, chiralMirror] <;>
    ring_nf <;> norm_num [bsCoeff_sq] <;> ring

theorem beamSplitter_preserves_intensity (v : Amp2) :
    intensity (beamSplitter v) = intensity v := by
  simp only [intensity, beamSplitter, Complex.normSq_mul, bsCoeff,
    Complex.normSq_ofReal, bsScale_mul_self, Complex.normSq_add, Complex.normSq_sub]
  ring

theorem mzi_passive_energy_conservation (φ : ℝ) (v : Amp2) :
    intensity (mziStep φ v) = intensity v := by
  simp only [mziStep, beamSplitter_preserves_intensity, phaseShift_preserves_intensity]

theorem chiralMirror_add (u v : Amp2) :
    chiralMirror (u + v) = chiralMirror u + chiralMirror v := by
  apply Prod.ext
  · rfl
  · change -(u.2 + v.2) = -u.2 + -v.2
    ring

theorem chiralMirror_smul (c : ℂ) (v : Amp2) :
    chiralMirror (c • v) = c • chiralMirror v := by
  apply Prod.ext <;> simp [chiralMirror]

theorem phaseShift_add (φ : ℝ) (u v : Amp2) :
    phaseShift φ (u + v) = phaseShift φ u + phaseShift φ v := by
  apply Prod.ext <;> simp [phaseShift, mul_add]

theorem phaseShift_smul (φ : ℝ) (c : ℂ) (v : Amp2) :
    phaseShift φ (c • v) = c • phaseShift φ v := by
  apply Prod.ext <;> simp [phaseShift, mul_left_comm]

theorem beamSplitter_add (u v : Amp2) :
    beamSplitter (u + v) = beamSplitter u + beamSplitter v := by
  apply Prod.ext <;> dsimp [beamSplitter] <;> ring

theorem beamSplitter_smul (c : ℂ) (v : Amp2) :
    beamSplitter (c • v) = c • beamSplitter v := by
  apply Prod.ext <;> dsimp [beamSplitter] <;> ring

theorem mzi_add (φ : ℝ) (u v : Amp2) :
    mziStep φ (u + v) = mziStep φ u + mziStep φ v := by
  simp only [mziStep, beamSplitter_add, phaseShift_add]

theorem mzi_smul (φ : ℝ) (c : ℂ) (v : Amp2) :
    mziStep φ (c • v) = c • mziStep φ v := by
  simp only [mziStep, beamSplitter_smul, phaseShift_smul]

theorem phaseShift_comp (φ ψ : ℝ) (v : Amp2) :
    phaseShift φ (phaseShift ψ v) = phaseShift (φ + ψ) v := by
  simp [phaseShift, phaseFactor_add, mul_assoc]

@[simp] theorem phaseShift_zero (v : Amp2) : phaseShift 0 v = v := by
  simp [phaseShift]

theorem phaseShift_pi (v : Amp2) : phaseShift Real.pi v = -chiralMirror v := by
  simp [phaseShift, chiralMirror]

theorem phaseShift_inverse (φ : ℝ) (v : Amp2) : phaseShift (-φ) (phaseShift φ v) = v := by
  rw [phaseShift_comp, neg_add_cancel, phaseShift_zero]

theorem mzi_comp (φ ψ : ℝ) (v : Amp2) :
    mziStep φ (mziStep ψ v) = mziStep (φ + ψ) v := by
  simp only [mziStep, beamSplitter_involution, phaseShift_comp]

@[simp] theorem mzi_zero (v : Amp2) : mziStep 0 v = v := by
  simp [mziStep, beamSplitter_involution]

/-- Minus swap is the exact amplitude identity in this convention. -/
theorem mzi_pi (v : Amp2) : mziStep Real.pi v = (-v.2, -v.1) := by
  apply Prod.ext <;> dsimp [mziStep, beamSplitter, phaseShift] <;>
    rw [phaseFactor_pi] <;> ring_nf <;> norm_num [bsCoeff_sq] <;> ring

theorem mzi_inverse (φ : ℝ) (v : Amp2) : mziStep (-φ) (mziStep φ v) = v := by
  rw [mzi_comp, neg_add_cancel, mzi_zero]

theorem mzi_inverse_right (φ : ℝ) (v : Amp2) : mziStep φ (mziStep (-φ) v) = v := by
  rw [mzi_comp, add_neg_cancel, mzi_zero]

/-- Squared Euclidean distance in amplitude coordinates is preserved. -/
theorem mzi_difference_intensity (φ : ℝ) (u v : Amp2) :
    intensity (mziStep φ u - mziStep φ v) = intensity (u - v) := by
  have hn : mziStep φ (-v) = -mziStep φ v := by simpa using mzi_smul φ (-1) v
  rw [sub_eq_add_neg, ← hn, ← mzi_add, ← sub_eq_add_neg, mzi_passive_energy_conservation]

theorem mzi_input_amplitudes (φ : ℝ) :
    mziStep φ (1, 0) = ((phaseFactor φ + 1) / 2, (phaseFactor φ - 1) / 2) := by
  apply Prod.ext <;> dsimp [mziStep, phaseShift, beamSplitter] <;>
    ring_nf <;> norm_num [bsCoeff_sq] <;> ring

theorem mzi_routing_first (φ : ℝ) :
    Complex.normSq (mziStep φ (1, 0)).1 = (1 + Real.cos φ) / 2 := by
  rw [mzi_input_amplitudes]
  simp only [Complex.normSq_div, Complex.normSq_add]
  norm_num
  ring

theorem mzi_routing_second (φ : ℝ) :
    Complex.normSq (mziStep φ (1, 0)).2 = (1 - Real.cos φ) / 2 := by
  rw [mzi_input_amplitudes]
  simp only [Complex.normSq_div, Complex.normSq_sub]
  norm_num
  ring

theorem mzi_constructive_destructive_routing (φ : ℝ) :
    Complex.normSq (mziStep φ (1, 0)).1 = (1 + Real.cos φ) / 2 ∧
    Complex.normSq (mziStep φ (1, 0)).2 = (1 - Real.cos φ) / 2 :=
  ⟨mzi_routing_first φ, mzi_routing_second φ⟩

theorem mzi_routing_half_angles (φ : ℝ) :
    Complex.normSq (mziStep φ (1, 0)).1 = Real.cos (φ / 2) ^ 2 ∧
    Complex.normSq (mziStep φ (1, 0)).2 = Real.sin (φ / 2) ^ 2 := by
  rw [mzi_routing_first, mzi_routing_second]
  have hc := Real.cos_two_mul (φ / 2)
  rw [show 2 * (φ / 2) = φ by ring] at hc
  constructor <;> nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]

theorem mzi_endpoint_amplitudes :
    mziStep 0 (1, 0) = (1, 0) ∧ mziStep Real.pi (1, 0) = (0, -1) := by
  simp [mzi_pi]

structure PhotonicsMachZehnderChiralSuite : Prop where
  mirror_involution : ∀ v : Amp2, chiralMirror (chiralMirror v) = v
  mirror_intensity : ∀ v : Amp2, intensity (chiralMirror v) = intensity v
  splitter_involution : ∀ v : Amp2, beamSplitter (beamSplitter v) = v
  splitter_intensity : ∀ v : Amp2, intensity (beamSplitter v) = intensity v
  phase_intensity : ∀ (φ : ℝ) (v : Amp2), intensity (phaseShift φ v) = intensity v
  mzi_intensity : ∀ (φ : ℝ) (v : Amp2), intensity (mziStep φ v) = intensity v
  routing : ∀ φ : ℝ,
    Complex.normSq (mziStep φ (1, 0)).1 = (1 + Real.cos φ) / 2 ∧
    Complex.normSq (mziStep φ (1, 0)).2 = (1 - Real.cos φ) / 2
  inverse_action : ∀ (φ : ℝ) (v : Amp2), mziStep (-φ) (mziStep φ v) = v
  difference_intensity : ∀ (φ : ℝ) (u v : Amp2),
    intensity (mziStep φ u - mziStep φ v) = intensity (u - v)

theorem verification_suite : PhotonicsMachZehnderChiralSuite := {
  mirror_involution := chiralMirror_involution
  mirror_intensity := chiralMirror_preserves_intensity
  splitter_involution := beamSplitter_involution
  splitter_intensity := beamSplitter_preserves_intensity
  phase_intensity := phaseShift_preserves_intensity
  mzi_intensity := mzi_passive_energy_conservation
  routing := mzi_constructive_destructive_routing
  inverse_action := mzi_inverse
  difference_intensity := mzi_difference_intensity
}

end
end PhotonicsMachZehnderChiralContract
