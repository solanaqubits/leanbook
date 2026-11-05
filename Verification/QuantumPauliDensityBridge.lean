/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPauliMatrix
import Verification.QuantumEntanglementSwappingPurificationContract

/-!
# Exact Pauli embedding and typed two-qubit depolarization

The parameter is the mixing probability with I₄/4, not the probability of a
nonidentity single-qubit Pauli error. Born weights and conditional Bell states
are reused from the existing ideal swapping protocol. No detector model or
fault-tolerant circuit threshold is asserted.
-/

noncomputable section
namespace QuantumPauliDensityBridge
open QuantumPauliMatrix QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract
open scoped BigOperators ComplexOrder

/-- Canonical embedding of the exact Gaussian-integer representation. -/
def toComplex (a : GI) : ℂ := (a.re : ℂ) + (a.im : ℂ) * Complex.I

theorem toComplex_add (a b : GI) : toComplex (ga a b) = toComplex a + toComplex b := by
  simp [toComplex, ga, Int.cast_add]; ring

theorem toComplex_mul (a b : GI) : toComplex (gm a b) = toComplex a * toComplex b := by
  simp [toComplex, gm, Int.cast_add, Int.cast_sub, Int.cast_mul]
  ring_nf
  simp
  ring

theorem toComplex_conjugate (a : GI) : toComplex (gc a) = star (toComplex a) := by
  simp [toComplex, gc]

theorem toComplex_injective : Function.Injective toComplex := by
  intro a b h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [toComplex] at hr hi
  cases a; cases b
  simp_all

instance basisFintype : (n : Nat) → Fintype (Basis n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd Bool (Basis n) inferInstance (basisFintype n)

/-- Entrywise complex embedding into ordinary Mathlib matrices. -/
def embed {n : Nat} (M : Mat n) : Matrix (Basis n) (Basis n) ℂ :=
  fun i j => toComplex (M i j)

theorem sumBasis_embedding (n : Nat) (f : Basis n → GI) :
    toComplex (sumBasis n f) = ∑ i, toComplex (f i) := by
  induction n with
  | zero => change toComplex (f ()) = ∑ i : Unit, toComplex (f i)
            simp
  | succ n ih =>
    change toComplex (ga (sumBasis n _) (sumBasis n _)) = _
    rw [toComplex_add, ih, ih]
    change _ = ∑ i : Bool × Basis n, toComplex (f i)
    rw [Fintype.sum_prod_type]
    simp [add_comm]

theorem embed_multiplication {n : Nat} (M N : Mat n) :
    embed (mm M N) = embed M * embed N := by
  ext i j
  simp only [embed, mm, Matrix.mul_apply, ← toComplex_mul]
  exact sumBasis_embedding n _

theorem embed_adjoint {n : Nat} (M : Mat n) :
    embed (adjoint M) = (embed M).conjTranspose := by
  ext i j
  exact toComplex_conjugate _

theorem pauli_complex_matrix_sound (p q : Pauli4QPhase) :
    embed (denote4 (mulPauli4Q p q)) = embed (denote4 p) * embed (denote4 q) := by
  rw [mulPauli4Q_matrix_sound, embed_multiplication]

theorem cnot_complex_conjugation_sound (phase : Phase) (a b : Axis) :
    embed cnotMatrix * embed (denote2 phase a b) * (embed cnotMatrix).conjTranspose =
      embed (denote2 (cnotPhase phase a b) (cnotControl a b) (cnotTarget a b)) := by
  rw [← embed_adjoint, ← embed_multiplication, ← embed_multiplication,
    cnot_conjugation_sound]

/-- Physical mixing probability represented by a bounded basis-point input. -/
def probability (p : BoundedBps) : ℝ := (p.val : ℝ) / 10000

theorem probability_bounds (p : BoundedBps) : 0 ≤ probability p ∧ probability p ≤ 1 := by
  have h0 : (0 : ℝ) ≤ p.val := by exact_mod_cast p.nonneg
  have h1 : (p.val : ℝ) ≤ 10000 := by exact_mod_cast p.le_scale
  dsimp [probability]; constructor <;> linarith

/-- Normalized positive two-qubit density, with no claim about preparation. -/
structure PairState where
  matrix : PairDensity
  positive : matrix.PosSemidef
  trace_one : matrix.trace = 1

def maximallyMixed : PairDensity := (1 / 4 : ℝ) • (1 : PairDensity)

theorem maximallyMixed_positive : maximallyMixed.PosSemidef :=
  Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)

theorem maximallyMixed_trace : maximallyMixed.trace = 1 := by
  norm_num [maximallyMixed, Matrix.trace_smul, Matrix.trace_one]

/-- Convex action on normalized density matrices; the input probability is bounded. -/
def depolarizeMatrix (p : BoundedBps) (ρ : PairDensity) : PairDensity :=
  (1 - probability p) • ρ + probability p • maximallyMixed

theorem depolarize_positive (p : BoundedBps) (ρ : PairState) :
    (depolarizeMatrix p ρ.matrix).PosSemidef := by
  exact (ρ.positive.smul (sub_nonneg.mpr (probability_bounds p).2)).add
    (maximallyMixed_positive.smul (probability_bounds p).1)

theorem depolarize_trace (p : BoundedBps) (ρ : PairState) :
    (depolarizeMatrix p ρ.matrix).trace = 1 := by
  simp [depolarizeMatrix, Matrix.trace_add, Matrix.trace_smul,
    ρ.trace_one, maximallyMixed_trace]

def depolarize (p : BoundedBps) (ρ : PairState) : PairState :=
  ⟨depolarizeMatrix p ρ.matrix, depolarize_positive p ρ, depolarize_trace p ρ⟩

theorem targetOverlap_add (ρ σ : PairDensity) :
    targetOverlap (ρ + σ) = targetOverlap ρ + targetOverlap σ := by
  simp [targetOverlap, mul_add, add_mul, Finset.sum_add_distrib]

theorem targetOverlap_real_smul (r : ℝ) (ρ : PairDensity) :
    targetOverlap (r • ρ) = (r : ℂ) * targetOverlap ρ := by
  simp only [targetOverlap, Matrix.smul_apply, Complex.real_smul]
  simp_rw [show ∀ i j : PairIndex,
    star (bellKet .phiPlus i.1 i.2) * ((r : ℂ) * ρ i j) * bellKet .phiPlus j.1 j.2 =
    (r : ℂ) * (star (bellKet .phiPlus i.1 i.2) * ρ i j * bellKet .phiPlus j.1 j.2)
    from fun _ _ => by ring]
  simp only [Finset.mul_sum]

theorem maximallyMixed_overlap : targetOverlap maximallyMixed = (1 / 4 : ℂ) := by
  simp [maximallyMixed, targetOverlap, Fintype.sum_prod_type, Fin.sum_univ_two,
    bellKet, Complex.real_smul]
  ring_nf
  norm_num [bellCoeff_sq]

/-- Squared fidelity with the fixed pure Bell target, derived from matrix entries. -/
theorem depolarize_overlap (p : BoundedBps) (ρ : PairState) :
    targetOverlap (depolarize p ρ).matrix =
      (1 - (probability p : ℂ)) * targetOverlap ρ.matrix + (probability p : ℂ) / 4 := by
  simp [depolarize, depolarizeMatrix, targetOverlap_add, targetOverlap_real_smul,
    maximallyMixed_overlap, div_eq_mul_inv]

/-- Exact connection to the integer numerator. The input fidelity premise is explicit. -/
theorem channelNumerator_matrix_sound (f p : BoundedBps) (ρ : PairState)
    (hf : targetOverlap ρ.matrix = (f.val : ℂ) / 10000) :
    targetOverlap (depolarize p ρ).matrix = (channelNumerator f p : ℂ) / 100000000 := by
  rw [depolarize_overlap, hf]
  simp [probability, channelNumerator, Int.cast_add, Int.cast_mul, Int.cast_sub]
  ring

/-- Discretization error in physical fidelity units: floor underestimates by < 10⁻⁴. -/
theorem channelFloor_matrix_error (f p : BoundedBps) (ρ : PairState)
    (hf : targetOverlap ρ.matrix = (f.val : ℂ) / 10000) :
    (channelFloor f p).val / (10000 : ℝ) ≤ (targetOverlap (depolarize p ρ).matrix).re ∧
    (targetOverlap (depolarize p ρ).matrix).re < ((channelFloor f p).val + 1) / (10000 : ℝ) := by
  rw [channelNumerator_matrix_sound f p ρ hf]
  have h := channel_rounding_bound f p
  have hlo : (10000 : ℝ) * (channelFloor f p).val ≤ channelNumerator f p := by exact_mod_cast h.1
  have hhi : (channelNumerator f p : ℝ) < 10000 * ((channelFloor f p).val + 1) := by
    exact_mod_cast h.2
  simp only [Complex.div_re, Complex.intCast_re, Complex.intCast_im]
  norm_num
  constructor <;> linarith

/-- Corrected conditional output of the already formalized ideal BSM protocol. -/
def correctedSwapState (m : BellMeasurement) : PairState :=
  { matrix := purePairDensity (correctOuter m (swappedOuter m))
    positive := pure_pair_positive _
    trace_one := by rw [swapping_exact_correction, pure_pair_trace, bell_pair_normalized]; rfl }

theorem correctedSwap_overlap (m : BellMeasurement) :
    targetOverlap (correctedSwapState m).matrix = 1 := by
  change targetOverlap (purePairDensity (correctOuter m (swappedOuter m))) = 1
  rw [swapping_exact_correction]
  have h := phase_density_fidelity 1
  simpa [phaseDensity] using h

/-- Jointly records the Born weight and post-correction noisy conditional overlap.
    The noise is applied after ideal correction; it is not a model of noisy BSM. -/
theorem born_and_noisy_conditional_fidelity (m : BellMeasurement) (p : BoundedBps) :
    swapOutcomeProbability m = (1 / 4 : ℝ) ∧
    targetOverlap (depolarize p (correctedSwapState m)).matrix =
      1 - 3 * (probability p : ℂ) / 4 := by
  refine ⟨swapping_success_probability m, ?_⟩
  rw [depolarize_overlap, correctedSwap_overlap]
  ring

/-- Integration contract: exact operators, physical states, scalar bridge, and Born scope. -/
structure QuantumPauliDensityBridgeSuite : Prop where
  gaussian_injective : Function.Injective toComplex
  multiplication : ∀ p q, embed (denote4 (mulPauli4Q p q)) =
    embed (denote4 p) * embed (denote4 q)
  conjugation : ∀ phase a b,
    embed cnotMatrix * embed (denote2 phase a b) * (embed cnotMatrix).conjTranspose =
      embed (denote2 (cnotPhase phase a b) (cnotControl a b) (cnotTarget a b))
  positive : ∀ p (ρ : PairState), (depolarizeMatrix p ρ.matrix).PosSemidef
  trace_one : ∀ p (ρ : PairState), (depolarizeMatrix p ρ.matrix).trace = 1
  scalar_bridge : ∀ (f p : BoundedBps) (ρ : PairState),
    targetOverlap ρ.matrix = (f.val : ℂ) / 10000 →
    targetOverlap (depolarize p ρ).matrix = (channelNumerator f p : ℂ) / 100000000
  rounding : ∀ (f p : BoundedBps) (ρ : PairState),
    targetOverlap ρ.matrix = (f.val : ℂ) / 10000 →
    (channelFloor f p).val / (10000 : ℝ) ≤ (targetOverlap (depolarize p ρ).matrix).re ∧
    (targetOverlap (depolarize p ρ).matrix).re < ((channelFloor f p).val + 1) / (10000 : ℝ)
  born_and_conditional : ∀ m p, swapOutcomeProbability m = (1 / 4 : ℝ) ∧
    targetOverlap (depolarize p (correctedSwapState m)).matrix =
      1 - 3 * (probability p : ℂ) / 4

theorem verification_suite : QuantumPauliDensityBridgeSuite :=
  ⟨toComplex_injective, pauli_complex_matrix_sound, cnot_complex_conjugation_sound,
    depolarize_positive, depolarize_trace, channelNumerator_matrix_sound,
    channelFloor_matrix_error, born_and_noisy_conditional_fidelity⟩

end QuantumPauliDensityBridge
