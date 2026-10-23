/-
Copyright (c) 2026 Leanbook contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

/-! Ideal Steane CSS code. Binary labels forget global phases; amplitude actions do not. -/
namespace QuantumSteaneCodeErrorCorrectionContract

abbrev Bit := ZMod 2
abbrev Word := Fin 7 → Bit
abbrev Ket := Word → ℂ

def dot (a b : Word) : Bit := ∑ j, a j * b j

def hRow : Fin 3 → Word :=
  ![![1, 0, 1, 0, 1, 0, 1], ![0, 1, 1, 0, 0, 1, 1], ![0, 0, 0, 1, 1, 1, 1]]

def syndrome (a : Word) : Fin 3 → Bit := fun i => dot (hRow i) a

def unitWord (j : Fin 7) : Word := fun k => if k = j then 1 else 0

def weight (a : Word) : ℕ := (Finset.univ.filter fun j => a j ≠ 0).card

def rowWord (r : Fin 3 → Bit) : Word := fun j => ∑ i, r i * hRow i j

def rowSpace (a : Word) : Prop := ∃ r, rowWord r = a

instance (a : Word) : Decidable (rowSpace a) := inferInstanceAs (Decidable (∃ _, _))

def ones : Word := fun _ => 1

theorem dot_add_right (a b c : Word) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_comm (a b : Word) : dot a b = dot b a := by simp [dot, mul_comm]

theorem word_add_self (a : Word) : a + a = 0 := by
  ext j
  exact (show ∀ x : Bit, x + x = 0 by decide) (a j)

theorem rows_orthogonal : ∀ i j, dot (hRow i) (hRow j) = 0 := by decide

theorem columns_nonzero : ∀ j, syndrome (unitWord j) ≠ 0 := by decide

theorem columns_injective : Function.Injective (fun j => syndrome (unitWord j)) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks all 128 binary words and their three parity checks.
theorem hamming_minimum : ∀ a : Word, syndrome a = 0 → weight a < 3 → a = 0 := by
  decide


noncomputable section

/-- Additive character of the binary field, retaining the physical Pauli sign. -/
def sign (b : Bit) : ℂ := if b = 0 then 1 else -1

theorem sign_add (a b : Bit) : sign (a + b) = sign a * sign b := by
  have cases_bit : ∀ x : Bit, x = 0 ∨ x = 1 := by decide
  rcases cases_bit a with rfl | rfl <;> rcases cases_bit b with rfl | rfl
  · simp [sign]
  · simp [sign]
  · simp [sign]
  · rw [show (1 : Bit) + 1 = 0 by decide]
    simp [sign]

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]

@[simp] theorem sign_square (a : Bit) : sign a * sign a = 1 := by
  by_cases h : a = 0 <;> simp [sign, h]

def xAction (a : Word) (ψ : Ket) : Ket := fun q => ψ (q + a)
def zAction (a : Word) (ψ : Ket) : Ket := fun q => sign (dot a q) * ψ q

def scale (c : ℂ) (ψ : Ket) : Ket := fun q => c * ψ q

@[simp] theorem scale_one (ψ : Ket) : scale 1 ψ = ψ := by
  ext q
  simp [scale]

/-- Normal order X^x Z^z; the scalar argument is an explicit global phase. -/
def pauliAction (phase : ℂ) (x z : Word) (ψ : Ket) : Ket :=
  scale phase (xAction x (zAction z ψ))

theorem x_add (a b : Word) (ψ : Ket) :
    xAction (a + b) ψ = xAction a (xAction b ψ) := by
  funext q
  simp [xAction, add_assoc]

theorem z_add (a b : Word) (ψ : Ket) :
    zAction (a + b) ψ = zAction a (zAction b ψ) := by
  funext q
  have hd : dot (a + b) q = dot a q + dot b q := by
    rw [dot_comm, dot_add_right, dot_comm q a, dot_comm q b]
  simp [zAction, hd, sign_add, mul_assoc]

@[simp] theorem x_zero (ψ : Ket) : xAction 0 ψ = ψ := by ext q; simp [xAction]
@[simp] theorem z_zero (ψ : Ket) : zAction 0 ψ = ψ := by ext q; simp [zAction, dot]

@[simp] theorem x_involution (a : Word) (ψ : Ket) : xAction a (xAction a ψ) = ψ := by
  rw [← x_add, word_add_self, x_zero]

@[simp] theorem z_involution (a : Word) (ψ : Ket) : zAction a (zAction a ψ) = ψ := by
  rw [← z_add, word_add_self, z_zero]

theorem x_z_commutation (a b : Word) (ψ : Ket) :
    xAction a (zAction b ψ) = scale (sign (dot b a)) (zAction b (xAction a ψ)) := by
  funext q
  simp only [xAction, zAction, scale, dot_add_right, sign_add]
  ring

theorem x_scale (a : Word) (c : ℂ) (ψ : Ket) :
    xAction a (scale c ψ) = scale c (xAction a ψ) := rfl

theorem z_scale (a : Word) (c : ℂ) (ψ : Ket) :
    zAction a (scale c ψ) = scale c (zAction a ψ) := by
  ext q
  simp [zAction, scale]
  ring

theorem xz_stabilizers_commute (i j : Fin 3) (ψ : Ket) :
    xAction (hRow i) (zAction (hRow j) ψ) =
      zAction (hRow j) (xAction (hRow i) ψ) := by
  rw [x_z_commutation, rows_orthogonal, sign_zero]
  ext q
  simp [scale]

def Codespace (ψ : Ket) : Prop :=
  ∀ i, xAction (hRow i) ψ = ψ ∧ zAction (hRow i) ψ = ψ

-- Finite field row-space enumeration; not an asserted code dimension.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks 128 words against the eight row-coefficient choices.
theorem rowspace_enumeration : ∀ a, rowSpace a ↔
    a = 0 ∨ a = hRow 0 ∨ a = hRow 1 ∨ a = hRow 2 ∨
    a = hRow 0 + hRow 1 ∨ a = hRow 0 + hRow 2 ∨ a = hRow 1 + hRow 2 ∨
    a = hRow 0 + (hRow 1 + hRow 2) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks both eight-word cosets for each of the 128 words.
theorem kernel_cosets : ∀ a, syndrome a = 0 ↔ rowSpace a ∨ rowSpace (a + ones) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks disjointness over all 128 words and row coefficients.
theorem cosets_disjoint : ∀ a, rowSpace a → ¬ rowSpace (a + ones) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the three translations on all 128 possible words.
theorem rowspace_shift : ∀ a i, rowSpace (a + hRow i) ↔ rowSpace a := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction counts the row-space predicate over all 128 words.
theorem rowspace_card : (Finset.univ.filter rowSpace).card = 8 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction counts the translated row-space predicate over 128 words.
theorem coset_card : (Finset.univ.filter fun a => rowSpace (a + ones)).card = 8 := by
  decide

theorem code_row_actions {ψ : Ket} (h : Codespace ψ) {a : Word} (ha : rowSpace a) :
    xAction a ψ = ψ ∧ zAction a ψ = ψ := by
  rcases (rowspace_enumeration a).mp ha with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
  all_goals subst a
  · simp
  · exact h 0
  · exact h 1
  · exact h 2
  all_goals simp [x_add, z_add, (h 0).1, (h 0).2, (h 1).1, (h 1).2, (h 2).1, (h 2).2]

/-- Unnormalized logical basis coordinates, useful for the exact eigenspace characterization. -/
def rawEncode (α β : ℂ) : Ket := fun q =>
  if rowSpace q then α else if rowSpace (q + ones) then β else 0

theorem rawEncode_in_codespace (α β : ℂ) : Codespace (rawEncode α β) := by
  intro i
  constructor
  · ext q
    simp only [xAction, rawEncode, rowspace_shift]
    simp [show q + hRow i + ones = q + ones + hRow i by abel, rowspace_shift]
  · ext q
    by_cases hq : syndrome q = 0
    · have hd : dot (hRow i) q = 0 := congrFun hq i
      simp [zAction, hd]
    · have hn := mt (kernel_cosets q).mpr hq
      simp only [not_or] at hn
      simp [zAction, rawEncode, hn.1, hn.2]

theorem codespace_characterization (ψ : Ket) :
    Codespace ψ ↔ ψ = rawEncode (ψ 0) (ψ ones) := by
  constructor
  · intro h
    ext q
    by_cases hd : rowSpace q
    · have he := congrFun (code_row_actions h hd).1 0
      simpa [xAction, rawEncode, hd] using he
    · by_cases hc : rowSpace (q + ones)
      · have he := congrFun (code_row_actions h hc).1 ones
        have hz : ones + (q + ones) = q := by
          calc
            _ = q + (ones + ones) := by abel
            _ = q := by rw [word_add_self, add_zero]
        simpa [xAction, rawEncode, hd, hc, hz] using he
      · have hq : syndrome q ≠ 0 := mt (kernel_cosets q).mp (not_or.mpr ⟨hd, hc⟩)
        have hex : ∃ i, dot (hRow i) q ≠ 0 := by
          by_contra hnone
          push Not at hnone
          exact hq (funext hnone)
        obtain ⟨i, hi⟩ := hex
        have he := congrFun (h i).2 q
        simp only [zAction, sign, if_neg hi, neg_one_mul] at he
        have he0 : ψ q = 0 := by linear_combination -(1 / 2 : ℂ) * he
        simp [rawEncode, hd, hc, he0]
  · intro h
    rw [h]
    exact rawEncode_in_codespace _ _


def ketNormSq (ψ : Ket) : ℝ := ∑ q, Complex.normSq (ψ q)

theorem rawEncode_norm (α β : ℂ) :
    ketNormSq (rawEncode α β) = 8 * (Complex.normSq α + Complex.normSq β) := by
  have hf : ∀ q, Complex.normSq (rawEncode α β q) =
      (if rowSpace q then Complex.normSq α else 0) +
      (if rowSpace (q + ones) then Complex.normSq β else 0) := by
    intro q
    by_cases hd : rowSpace q
    · simp [rawEncode, hd, cosets_disjoint q hd]
    · by_cases hc : rowSpace (q + ones) <;> simp [rawEncode, hd, hc]
  unfold ketNormSq
  simp_rw [hf]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, rowspace_card, coset_card]
  ring

def normFactor : ℂ := ((1 / Real.sqrt 8 : ℝ) : ℂ)

theorem normFactor_normSq : Complex.normSq normFactor = 1 / 8 := by
  norm_num [normFactor, Complex.normSq_ofReal, Real.sq_sqrt]

/-- Isometric encoder of one arbitrary complex qubit into seven physical qubits. -/
def encode (α β : ℂ) : Ket := rawEncode (normFactor * α) (normFactor * β)

theorem encoding_isometry (α β : ℂ) :
    ketNormSq (encode α β) = Complex.normSq α + Complex.normSq β := by
  rw [encode, rawEncode_norm, Complex.normSq_mul, Complex.normSq_mul, normFactor_normSq]
  ring

theorem encoding_codespace (α β : ℂ) : Codespace (encode α β) :=
  rawEncode_in_codespace _ _

theorem rawEncode_at_zero (α β : ℂ) : rawEncode α β 0 = α := by
  have h : rowSpace 0 := by decide
  simp [rawEncode, h]

theorem rawEncode_at_ones (α β : ℂ) : rawEncode α β ones = β := by
  have h : ¬ rowSpace ones := by decide
  have h0 : rowSpace 0 := by decide
  simp [rawEncode, h, word_add_self, h0]

theorem normFactor_ne_zero : normFactor ≠ 0 := by
  intro h
  have hn := normFactor_normSq
  rw [h, map_zero] at hn
  norm_num at hn

theorem encoding_injective : Function.Injective (fun p : ℂ × ℂ => encode p.1 p.2) := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h ones
  simp only [encode, rawEncode_at_zero] at h0
  simp only [encode, rawEncode_at_ones] at h1
  exact Prod.ext (mul_left_cancel₀ normFactor_ne_zero h0)
    (mul_left_cancel₀ normFactor_ne_zero h1)

theorem encoding_add (a b c d : ℂ) : encode (a + c) (b + d) = encode a b + encode c d := by
  ext q
  simp only [encode, rawEncode, Pi.add_apply]
  split_ifs <;> ring

theorem encoding_smul (c a b : ℂ) : encode (c * a) (c * b) = scale c (encode a b) := by
  ext q
  simp only [encode, rawEncode, scale]
  split_ifs <;> ring

/-- Exactly two complex coordinates, proved from all six stabilizer equations. -/
theorem codespace_exactly_one_qubit (ψ : Ket) :
    Codespace ψ ↔ ∃! p : ℂ × ℂ, encode p.1 p.2 = ψ := by
  constructor
  · intro h
    refine ⟨(ψ 0 / normFactor, ψ ones / normFactor), ?_, ?_⟩
    · simpa [encode, mul_div_cancel₀ _ normFactor_ne_zero] using
        (codespace_characterization ψ).mp h |>.symm
    · intro p hp
      apply encoding_injective
      simpa [encode, mul_div_cancel₀ _ normFactor_ne_zero] using
        hp.trans ((codespace_characterization ψ).mp h)
  · rintro ⟨p, hp, _⟩
    rw [← hp]
    exact encoding_codespace _ _

abbrev SingleError := Fin 3 × Fin 7
abbrev BinaryPauli := Word × Word
abbrev SyndromePair := (Fin 3 → Bit) × (Fin 3 → Bit)

/-- Kind 0 is X, kind 1 is Z, kind 2 is canonical Y=iXZ. -/
def singleLabel (e : SingleError) : BinaryPauli :=
  if e.1 = 0 then (unitWord e.2, 0)
  else if e.1 = 1 then (0, unitWord e.2) else (unitWord e.2, unitWord e.2)

def pauliSyndrome (p : BinaryPauli) : SyndromePair := (syndrome p.1, syndrome p.2)

def allSingleErrors : List SingleError :=
  (List.finRange 3).flatMap fun k => (List.finRange 7).map fun j => (k, j)

def decodeSyndrome (s : SyndromePair) : Option SingleError :=
  allSingleErrors.find? fun e => pauliSyndrome (singleLabel e) == s

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the finite decoder search for each of 21 single errors.
theorem single_syndrome_decodes : ∀ e,
    decodeSyndrome (pauliSyndrome (singleLabel e)) = some e := by decide

theorem single_syndromes_unique : Function.Injective (pauliSyndrome ∘ singleLabel) := by
  intro a b h
  have hd := congrArg decodeSyndrome h
  simpa only [Function.comp_apply, single_syndrome_decodes, Option.some.injEq] using hd

theorem identity_syndrome_decodes : decodeSyndrome (0, 0) = none := by decide

def applySingleError (e : SingleError) (ψ : Ket) : Ket :=
  if e.1 = 0 then xAction (unitWord e.2) ψ
  else if e.1 = 1 then zAction (unitWord e.2) ψ
  else scale Complex.I (xAction (unitWord e.2) (zAction (unitWord e.2) ψ))

theorem unit_self_dot (j : Fin 7) : dot (unitWord j) (unitWord j) = 1 := by
  revert j
  decide

theorem canonical_y_involution (j : Fin 7) (ψ : Ket) :
    applySingleError (2, j) (applySingleError (2, j) ψ) = ψ := by
  ext q
  have hq : q + unitWord j + unitWord j = q := by
    rw [add_assoc, word_add_self, add_zero]
  simp only [applySingleError, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_false, xAction, zAction, scale, hq,
    dot_add_right, unit_self_dot, sign_add]
  simp only [sign, show (1 : Bit) ≠ 0 by decide, if_false]
  by_cases hd : dot (unitWord j) q = 0 <;> simp [hd, ← mul_assoc]

theorem single_error_involution (e : SingleError) (ψ : Ket) :
    applySingleError e (applySingleError e ψ) = ψ := by
  rcases e with ⟨k, j⟩
  fin_cases k
  · simp [applySingleError]
  · simp [applySingleError]
  · exact canonical_y_involution j ψ

def recover (s : SyndromePair) (ψ : Ket) : Ket :=
  match decodeSyndrome s with
  | none => ψ
  | some e => applySingleError e ψ

/-- Exact vector recovery for canonical I/X/Z/Y, not for unknown global phases. -/
theorem single_error_exact_recovery (e : SingleError) (ψ : Ket) :
    recover (pauliSyndrome (singleLabel e)) (applySingleError e ψ) = ψ := by
  simp [recover, single_syndrome_decodes, single_error_involution]


theorem identity_exact_recovery (ψ : Ket) : recover (0, 0) ψ = ψ := by
  simp [recover, identity_syndrome_decodes]

theorem x_actions_commute (a b : Word) (ψ : Ket) :
    xAction a (xAction b ψ) = xAction b (xAction a ψ) := by
  rw [← x_add, ← x_add, add_comm]

theorem z_actions_commute (a b : Word) (ψ : Ket) :
    zAction a (zAction b ψ) = zAction b (zAction a ψ) := by
  rw [← z_add, ← z_add, add_comm]

theorem z_x_commutation (a b : Word) (ψ : Ket) :
    zAction a (xAction b ψ) = scale (sign (dot a b)) (xAction b (zAction a ψ)) := by
  ext q
  simp only [zAction, xAction, scale, dot_add_right, sign_add]
  have hs := sign_square (dot a b)
  linear_combination -(sign (dot a q) * ψ (q + b)) * hs

/-- Actual stabilizer eigenvalues of an erroneous code ket, with arbitrary explicit phase. -/
theorem error_stabilizer_eigenvalues (phase : ℂ) (x z : Word) {ψ : Ket}
    (hψ : Codespace ψ) (i : Fin 3) :
    xAction (hRow i) (pauliAction phase x z ψ) =
      scale (sign (syndrome z i)) (pauliAction phase x z ψ) ∧
    zAction (hRow i) (pauliAction phase x z ψ) =
      scale (sign (syndrome x i)) (pauliAction phase x z ψ) := by
  constructor
  · rw [pauliAction, x_scale, x_actions_commute, x_z_commutation, (hψ i).1, x_scale]
    ext q
    simp only [scale, syndrome, dot_comm z (hRow i)]
    ring
  · rw [pauliAction, z_scale, z_x_commutation, z_actions_commute, (hψ i).2]
    ext q
    simp only [scale, syndrome]
    ring

/-- A check's spectral projection. An eigenstate with the requested sign is unchanged. -/
def checkProjector (check : Ket → Ket) (bit : Bit) (ψ : Ket) : Ket :=
  fun q => (ψ q + sign bit * check ψ q) / 2

theorem check_projection_on_eigenstate (check : Ket → Ket) (bit : Bit) (ψ : Ket)
    (h : check ψ = scale (sign bit) ψ) : checkProjector check bit ψ = ψ := by
  ext q
  rw [checkProjector, h]
  dsimp [scale]
  have hs := sign_square bit
  linear_combination (ψ q / 2) * hs

theorem row_ones_dot (i : Fin 3) : dot (hRow i) ones = 0 := by revert i; decide

theorem ones_self_dot : dot ones ones = 1 := by decide

def logicalX : Ket → Ket := xAction ones
def logicalZ : Ket → Ket := zAction ones

theorem logical_anticommutation (ψ : Ket) :
    logicalX (logicalZ ψ) = scale (-1) (logicalZ (logicalX ψ)) := by
  simpa [logicalX, logicalZ, ones_self_dot, sign] using x_z_commutation ones ones ψ

theorem logical_commutes_stabilizers (i : Fin 3) (ψ : Ket) :
    logicalX (xAction (hRow i) ψ) = xAction (hRow i) (logicalX ψ) ∧
    logicalX (zAction (hRow i) ψ) = zAction (hRow i) (logicalX ψ) ∧
    logicalZ (xAction (hRow i) ψ) = xAction (hRow i) (logicalZ ψ) ∧
    logicalZ (zAction (hRow i) ψ) = zAction (hRow i) (logicalZ ψ) := by
  refine ⟨x_actions_commute _ _ _, ?_, ?_, z_actions_commute _ _ _⟩
  · rw [logicalX, x_z_commutation, row_ones_dot, sign_zero]
    ext q
    simp [scale]
  · rw [logicalZ, z_x_commutation, dot_comm, row_ones_dot, sign_zero]
    ext q
    simp [scale]

theorem logicalX_on_encoding (α β : ℂ) : logicalX (encode α β) = encode β α := by
  ext q
  have hq : q + ones + ones = q := by rw [add_assoc, word_add_self, add_zero]
  by_cases hd : rowSpace q
  · simp [logicalX, xAction, encode, rawEncode, hd, cosets_disjoint q hd, hq]
  · by_cases hc : rowSpace (q + ones) <;>
      simp [logicalX, xAction, encode, rawEncode, hd, hc, hq]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the character on both cosets for all 128 words.
theorem parity_on_cosets : ∀ q, (rowSpace q → dot ones q = 0) ∧
    (rowSpace (q + ones) → dot ones q = 1) := by decide

theorem logicalZ_on_encoding (α β : ℂ) : logicalZ (encode α β) = encode α (-β) := by
  ext q
  by_cases hd : rowSpace q
  · simp [logicalZ, zAction, encode, rawEncode, hd, (parity_on_cosets q).1 hd]
  · by_cases hc : rowSpace (q + ones)
    · simp [logicalZ, zAction, encode, rawEncode, hd, hc, (parity_on_cosets q).2 hc, sign]
    · simp [logicalZ, zAction, encode, rawEncode, hd, hc]

/-- Projective Pauli centralizer: global scalar phases are not distance-bearing errors. -/
def InCentralizer (p : BinaryPauli) : Prop := syndrome p.1 = 0 ∧ syndrome p.2 = 0

def InStabilizerLabels (p : BinaryPauli) : Prop := rowSpace p.1 ∧ rowSpace p.2

instance (p : BinaryPauli) : Decidable (InCentralizer p) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (p : BinaryPauli) : Decidable (InStabilizerLabels p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def pauliWeight (p : BinaryPauli) : ℕ :=
  (Finset.univ.filter fun j => p.1 j ≠ 0 ∨ p.2 j ≠ 0).card

theorem component_weight_le (p : BinaryPauli) : weight p.1 ≤ pauliWeight p ∧
    weight p.2 ≤ pauliWeight p := by
  constructor
  · apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact Or.inl hj
  · apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact Or.inr hj

theorem centralizer_weight_lt_three (p : BinaryPauli) (hp : InCentralizer p)
    (hw : pauliWeight p < 3) : p = (0, 0) := by
  exact Prod.ext (hamming_minimum p.1 hp.1 (lt_of_le_of_lt (component_weight_le p).1 hw))
    (hamming_minimum p.2 hp.2 (lt_of_le_of_lt (component_weight_le p).2 hw))

def logicalWeightThree : BinaryPauli := (![1, 1, 1, 0, 0, 0, 0], 0)

theorem logical_weight_three_witness :
    InCentralizer logicalWeightThree ∧ ¬ InStabilizerLabels logicalWeightThree ∧
      pauliWeight logicalWeightThree = 3 := by decide

/-- Exact distance modulo global phases and stabilizer labels. -/
theorem steane_distance_exactly_three :
    (∀ p, InCentralizer p → ¬ InStabilizerLabels p → 3 ≤ pauliWeight p) ∧
    (∃ p, InCentralizer p ∧ ¬ InStabilizerLabels p ∧ pauliWeight p = 3) := by
  constructor
  · intro p hp hn
    by_contra hw
    have he := centralizer_weight_lt_three p hp (Nat.lt_of_not_ge hw)
    subst p
    exact hn (by decide)
  · exact ⟨logicalWeightThree, logical_weight_three_witness⟩

/-- Representative X^x Z^z for stabilizer labels; arbitrary scalar phases are excluded. -/
theorem stabilizer_label_fixes_code (p : BinaryPauli) (hp : InStabilizerLabels p)
    {ψ : Ket} (hψ : Codespace ψ) : pauliAction 1 p.1 p.2 ψ = ψ := by
  rw [pauliAction, (code_row_actions hψ hp.2).2, (code_row_actions hψ hp.1).1]
  ext q
  simp [scale]


theorem centralizer_preserves_codespace (p : BinaryPauli) (hp : InCentralizer p)
    (phase : ℂ) {ψ : Ket} (hψ : Codespace ψ) : Codespace (pauliAction phase p.1 p.2 ψ) := by
  intro i
  have h := error_stabilizer_eigenvalues phase p.1 p.2 hψ i
  have hx : syndrome p.1 i = 0 := congrFun hp.1 i
  have hz : syndrome p.2 i = 0 := congrFun hp.2 i
  simpa only [hx, hz, sign_zero, scale_one] using h

theorem weight_three_acts_logically {ψ : Ket} (hψ : Codespace ψ) :
    xAction logicalWeightThree.1 ψ = logicalX ψ := by
  have hw : logicalWeightThree.1 = ones + hRow 2 := by decide
  rw [hw, x_add, (hψ 2).1]
  rfl

theorem steane_code_distance :
    (∀ p, InCentralizer p → ¬ InStabilizerLabels p → 3 ≤ pauliWeight p) ∧
    (∃ p, InCentralizer p ∧ ¬ InStabilizerLabels p ∧ pauliWeight p = 3) :=
  steane_distance_exactly_three

theorem single_error_detection (e : SingleError) :
    pauliSyndrome (singleLabel e) ≠ (0, 0) := by
  intro h
  have hd := single_syndrome_decodes e
  rw [h, identity_syndrome_decodes] at hd
  contradiction

theorem single_error_correction (e : SingleError) (ψ : Ket) :
    recover (pauliSyndrome (singleLabel e)) (applySingleError e ψ) = ψ :=
  single_error_exact_recovery e ψ

theorem single_as_pauli (e : SingleError) (ψ : Ket) :
    applySingleError e ψ =
      pauliAction (if e.1 = 2 then Complex.I else 1) (singleLabel e).1 (singleLabel e).2 ψ := by
  rcases e with ⟨k, j⟩
  fin_cases k <;> ext q <;> simp [applySingleError, singleLabel, pauliAction, scale]

theorem single_error_eigenvalues (e : SingleError) {ψ : Ket} (hψ : Codespace ψ)
    (i : Fin 3) :
    xAction (hRow i) (applySingleError e ψ) =
      scale (sign ((pauliSyndrome (singleLabel e)).2 i)) (applySingleError e ψ) ∧
    zAction (hRow i) (applySingleError e ψ) =
      scale (sign ((pauliSyndrome (singleLabel e)).1 i)) (applySingleError e ψ) := by
  rw [single_as_pauli]
  exact error_stabilizer_eigenvalues _ _ _ hψ i

abbrev StabilizerIndex := Fin 2 × Fin 3

def stabilizerAction (i : StabilizerIndex) : Ket → Ket :=
  if i.1 = 0 then xAction (hRow i.2) else zAction (hRow i.2)

/-- All six actual operators commute, including XX, ZZ, and both cross orders. -/
theorem stabilizers_commute (i j : StabilizerIndex) (ψ : Ket) :
    stabilizerAction i (stabilizerAction j ψ) =
      stabilizerAction j (stabilizerAction i ψ) := by
  rcases i with ⟨a, i⟩
  rcases j with ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> simp only [stabilizerAction]
  · exact x_actions_commute _ _ _
  · exact xz_stabilizers_commute _ _ _
  · exact (xz_stabilizers_commute _ _ _).symm
  · exact z_actions_commute _ _ _

def checkBit (s : SyndromePair) (i : StabilizerIndex) : Bit :=
  if i.1 = 0 then s.2 i.2 else s.1 i.2

def allChecks : List StabilizerIndex :=
  (List.finRange 2).flatMap fun k => (List.finRange 3).map fun i => (k, i)

/-- Sequential ideal spectral projectors, not a physical ancilla circuit model. -/
def syndromeProjection (s : SyndromePair) (ψ : Ket) : Ket :=
  allChecks.foldl (fun φ i => checkProjector (stabilizerAction i) (checkBit s i) φ) ψ

theorem single_error_correct_projection (e : SingleError) {ψ : Ket} (hψ : Codespace ψ) :
    syndromeProjection (pauliSyndrome (singleLabel e)) (applySingleError e ψ) =
      applySingleError e ψ := by
  have hf : ∀ i : StabilizerIndex,
      checkProjector (stabilizerAction i) (checkBit (pauliSyndrome (singleLabel e)) i)
        (applySingleError e ψ) = applySingleError e ψ := by
    intro i
    apply check_projection_on_eigenstate
    rcases i with ⟨k, i⟩
    fin_cases k
    · exact (single_error_eigenvalues e hψ i).1
    · exact (single_error_eigenvalues e hψ i).2
  have hl : ∀ l : List StabilizerIndex,
      l.foldl (fun φ i => checkProjector (stabilizerAction i)
        (checkBit (pauliSyndrome (singleLabel e)) i) φ) (applySingleError e ψ) =
        applySingleError e ψ := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simpa only [List.foldl_cons, hf] using ih
  exact hl allChecks

theorem logical_operators_preservation {ψ : Ket} (hψ : Codespace ψ) :
    Codespace (logicalX ψ) ∧ Codespace (logicalZ ψ) := by
  obtain ⟨p, hp, _⟩ := (codespace_exactly_one_qubit ψ).mp hψ
  rw [← hp, logicalX_on_encoding, logicalZ_on_encoding]
  exact ⟨encoding_codespace _ _, encoding_codespace _ _⟩

theorem x_norm_preservation (a : Word) (ψ : Ket) :
    ketNormSq (xAction a ψ) = ketNormSq ψ := by
  exact Equiv.sum_comp (Equiv.addRight a) (fun q => Complex.normSq (ψ q))

theorem sign_normSq (b : Bit) : Complex.normSq (sign b) = 1 := by
  by_cases h : b = 0 <;> simp [sign, h]

theorem z_norm_preservation (a : Word) (ψ : Ket) :
    ketNormSq (zAction a ψ) = ketNormSq ψ := by
  simp [ketNormSq, zAction, Complex.normSq_mul, sign_normSq]

theorem scale_norm (c : ℂ) (ψ : Ket) :
    ketNormSq (scale c ψ) = Complex.normSq c * ketNormSq ψ := by
  simp [ketNormSq, scale, Complex.normSq_mul, Finset.mul_sum]

theorem single_error_isometry (e : SingleError) (ψ : Ket) :
    ketNormSq (applySingleError e ψ) = ketNormSq ψ := by
  rcases e with ⟨k, j⟩
  fin_cases k <;>
    simp [applySingleError, scale_norm, x_norm_preservation, z_norm_preservation]

theorem pauli_action_add (c : ℂ) (x z : Word) (ψ φ : Ket) :
    pauliAction c x z (ψ + φ) = pauliAction c x z ψ + pauliAction c x z φ := by
  ext q
  simp [pauliAction, scale, xAction, zAction, mul_add]

theorem pauli_action_smul (c d : ℂ) (x z : Word) (ψ : Ket) :
    pauliAction c x z (scale d ψ) = scale d (pauliAction c x z ψ) := by
  ext q
  simp only [pauliAction, scale, xAction, zAction]
  ring

/-- A concrete two-X error aliases a single-X syndrome and leaves a logical error. -/
theorem two_error_alias :
    pauliSyndrome (unitWord 0 + unitWord 1, 0) = pauliSyndrome (singleLabel (0, 2)) ∧
    unitWord 0 + unitWord 1 + unitWord 2 = logicalWeightThree.1 := by decide

theorem two_error_miscorrection (α β : ℂ) :
    recover (pauliSyndrome (unitWord 0 + unitWord 1, 0))
      (xAction (unitWord 0 + unitWord 1) (encode α β)) = encode β α := by
  rw [two_error_alias.1]
  simp only [recover, single_syndrome_decodes]
  change xAction (unitWord 2) (xAction (unitWord 0 + unitWord 1) (encode α β)) = _
  rw [← x_add, add_comm, two_error_alias.2,
    weight_three_acts_logically (encoding_codespace α β), logicalX_on_encoding]


/-- Phase-aware operator commutation, before restricting to code vectors. -/
theorem pauli_check_commutation (phase : ℂ) (x z : Word) (ψ : Ket) (i : Fin 3) :
    xAction (hRow i) (pauliAction phase x z ψ) =
      scale (sign (syndrome z i)) (pauliAction phase x z (xAction (hRow i) ψ)) ∧
    zAction (hRow i) (pauliAction phase x z ψ) =
      scale (sign (syndrome x i)) (pauliAction phase x z (zAction (hRow i) ψ)) := by
  constructor
  · rw [pauliAction, x_scale, x_actions_commute, x_z_commutation, x_scale]
    ext q
    simp only [pauliAction, scale, syndrome, dot_comm z (hRow i)]
    ring
  · rw [pauliAction, z_scale, z_x_commutation, z_actions_commute]
    ext q
    simp only [pauliAction, scale, syndrome]
    ring

theorem centralizer_commutes_checks (p : BinaryPauli) (hp : InCentralizer p)
    (ψ : Ket) (i : Fin 3) :
    xAction (hRow i) (pauliAction 1 p.1 p.2 ψ) =
      pauliAction 1 p.1 p.2 (xAction (hRow i) ψ) ∧
    zAction (hRow i) (pauliAction 1 p.1 p.2 ψ) =
      pauliAction 1 p.1 p.2 (zAction (hRow i) ψ) := by
  have hx : syndrome p.1 i = 0 := congrFun hp.1 i
  have hz : syndrome p.2 i = 0 := congrFun hp.2 i
  simpa only [hx, hz, sign_zero, scale_one] using pauli_check_commutation 1 p.1 p.2 ψ i

/-- The phase-free XZ representative squares to -I, unlike canonical Y=iXZ. -/
theorem unsigned_xz_square (j : Fin 7) (ψ : Ket) :
    xAction (unitWord j) (zAction (unitWord j)
      (xAction (unitWord j) (zAction (unitWord j) ψ))) = scale (-1) ψ := by
  rw [z_x_commutation, unit_self_dot, x_scale, x_involution, z_involution]
  simp [sign]

structure QuantumSteaneCodeErrorCorrectionSuite : Prop where
  parity_orthogonal : ∀ i j, dot (hRow i) (hRow j) = 0
  commute : ∀ i j ψ, stabilizerAction i (stabilizerAction j ψ) =
    stabilizerAction j (stabilizerAction i ψ)
  code_coordinates : ∀ ψ, Codespace ψ ↔ ∃! p : ℂ × ℂ, encode p.1 p.2 = ψ
  encoding_norm : ∀ α β, ketNormSq (encode α β) = Complex.normSq α + Complex.normSq β
  encoding_linear_add : ∀ a b c d, encode (a + c) (b + d) = encode a b + encode c d
  encoding_linear_smul : ∀ c a b, encode (c * a) (c * b) = scale c (encode a b)
  detection : ∀ e, pauliSyndrome (singleLabel e) ≠ (0, 0)
  unique_syndromes : Function.Injective (pauliSyndrome ∘ singleLabel)
  decoder : ∀ e, decodeSyndrome (pauliSyndrome (singleLabel e)) = some e
  correction : ∀ e ψ, recover (pauliSyndrome (singleLabel e)) (applySingleError e ψ) = ψ
  identity_correction : ∀ ψ, recover (0, 0) ψ = ψ
  error_norm : ∀ e ψ, ketNormSq (applySingleError e ψ) = ketNormSq ψ
  measured_syndrome : ∀ e ψ, Codespace ψ →
    syndromeProjection (pauliSyndrome (singleLabel e)) (applySingleError e ψ) =
      applySingleError e ψ
  logical_preservation : ∀ ψ, Codespace ψ →
    Codespace (logicalX ψ) ∧ Codespace (logicalZ ψ)
  logical_anti : ∀ ψ, logicalX (logicalZ ψ) = scale (-1) (logicalZ (logicalX ψ))
  logical_x : ∀ a b, logicalX (encode a b) = encode b a
  logical_z : ∀ a b, logicalZ (encode a b) = encode a (-b)
  distance_lower : ∀ p, InCentralizer p → ¬ InStabilizerLabels p → 3 ≤ pauliWeight p
  distance_upper : InCentralizer logicalWeightThree ∧
    ¬ InStabilizerLabels logicalWeightThree ∧ pauliWeight logicalWeightThree = 3
  centralizer_bridge : ∀ p, InCentralizer p → ∀ ψ i,
    xAction (hRow i) (pauliAction 1 p.1 p.2 ψ) =
      pauliAction 1 p.1 p.2 (xAction (hRow i) ψ) ∧
    zAction (hRow i) (pauliAction 1 p.1 p.2 ψ) =
      pauliAction 1 p.1 p.2 (zAction (hRow i) ψ)
  nontrivial_upper_witness : ∀ ψ, Codespace ψ →
    xAction logicalWeightThree.1 ψ = logicalX ψ
  multi_error_limit : ∀ a b, recover (pauliSyndrome (unitWord 0 + unitWord 1, 0))
    (xAction (unitWord 0 + unitWord 1) (encode a b)) = encode b a

theorem verification_suite : QuantumSteaneCodeErrorCorrectionSuite where
  parity_orthogonal := rows_orthogonal
  commute := stabilizers_commute
  code_coordinates := codespace_exactly_one_qubit
  encoding_norm := encoding_isometry
  encoding_linear_add := encoding_add
  encoding_linear_smul := encoding_smul
  detection := single_error_detection
  unique_syndromes := single_syndromes_unique
  decoder := single_syndrome_decodes
  correction := single_error_correction
  identity_correction := identity_exact_recovery
  error_norm := single_error_isometry
  measured_syndrome := fun e _ h => single_error_correct_projection e h
  logical_preservation := fun _ h => logical_operators_preservation h
  logical_anti := logical_anticommutation
  logical_x := logicalX_on_encoding
  logical_z := logicalZ_on_encoding
  distance_lower := steane_code_distance.1
  distance_upper := logical_weight_three_witness
  centralizer_bridge := centralizer_commutes_checks
  nontrivial_upper_witness := fun _ h => weight_three_acts_logically h
  multi_error_limit := two_error_miscorrection

end
end QuantumSteaneCodeErrorCorrectionContract
