/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAPedersenOpeningConsistencyContract
import Verification.CryptoSchnorrIdentification

/-! Full-vector hidden inner-product protocol. Three supplied accepting transcripts
extract a witness or a generator relation. Exact HVZK additionally requires bijective
blinding. No compressed IPA, adversarial fork acquisition, ROM or runtime claim. -/
namespace CryptoHiddenScalarInnerProductProtocolContract
open scoped BigOperators
open CryptoBulletproofsInnerProduct
namespace Range
export CryptoBulletproofsRangeReduction (Generators)
export CryptoBulletproofsRangeWitnessExtraction (RelationCoefficients relation_eval)
end Range
namespace Interp
export CryptoBulletproofsWitnessExtraction (interpolate_quad interpolate_quad_evaluates
  polynomial_interpolation_quad)
end Interp
variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A] {k : ℕ}

structure Claim (q : ℕ) (A : Type) (k : ℕ) where
  generators : Range.Generators q A k
  P : A
  V : A

structure Witness (q k : ℕ) where
  a : Vec k (ZMod q)
  b : Vec k (ZMod q)
  rho : ZMod q
  deriving DecidableEq

def linear (p : Claim q A k) (a b : Vec k (ZMod q)) : A :=
  multiscalar_mul a p.generators.G + multiscalar_mul b p.generators.H

def WitnessValid (p : Claim q A k) (w : Witness q k) : Prop :=
  linear p w.a w.b = p.P ∧
  dot_product w.a w.b • p.generators.B + w.rho • p.generators.Hblind = p.V

@[ext] structure Announcement (A : Type) where
  mask : A
  constant : A
  slope : A
  deriving DecidableEq

structure Response (q k : ℕ) where
  left : Vec k (ZMod q)
  right : Vec k (ZMod q)
  blind : ZMod q
  deriving DecidableEq

@[ext] structure Transcript (q : ℕ) (A : Type) (k : ℕ) where
  announcement : Announcement A
  challenge : ZMod q
  response : Response q k
  deriving DecidableEq

abbrev MaskRandomness (q k : ℕ) :=
  Vec k (ZMod q) × Vec k (ZMod q) × ZMod q × ZMod q

def cross (s t a b : Vec k (ZMod q)) : ZMod q := dot_product s b + dot_product a t

def commit (p : Claim q A k) (w : Witness q k) (r : MaskRandomness q k) : Announcement A :=
  ⟨linear p r.1 r.2.1,
   dot_product r.1 r.2.1 • p.generators.B + r.2.2.1 • p.generators.Hblind,
   cross r.1 r.2.1 w.a w.b • p.generators.B + r.2.2.2 • p.generators.Hblind⟩

def respond (w : Witness q k) (r : MaskRandomness q k) (e : ZMod q) : Response q k :=
  ⟨r.1 + e • w.a, r.2.1 + e • w.b, r.2.2.1 + e * r.2.2.2 + e ^ 2 * w.rho⟩

def honestTranscript (p : Claim q A k) (w : Witness q k) (r : MaskRandomness q k)
    (e : ZMod q) : Transcript q A k := ⟨commit p w r, e, respond w r e⟩

def Verify (p : Claim q A k) (tr : Transcript q A k) : Prop :=
  linear p tr.response.left tr.response.right = tr.announcement.mask + tr.challenge • p.P ∧
  dot_product tr.response.left tr.response.right • p.generators.B +
    tr.response.blind • p.generators.Hblind =
    tr.announcement.constant + tr.challenge • tr.announcement.slope + tr.challenge ^ 2 • p.V

instance [DecidableEq A] (p : Claim q A k) (tr : Transcript q A k) :
    Decidable (Verify p tr) := inferInstanceAs (Decidable (_ ∧ _))
instance [DecidableEq A] (p : Claim q A k) (w : Witness q k) :
    Decidable (WitnessValid p w) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem linear_add (p : Claim q A k) (a b c d : Vec k (ZMod q)) :
    linear p (a + c) (b + d) = linear p a b + linear p c d := by
  simp [linear, multiscalar_mul, add_smul, Finset.sum_add_distrib]; abel

@[simp] theorem linear_smul (p : Claim q A k) (e : ZMod q) (a b : Vec k (ZMod q)) :
    linear p (e • a) (e • b) = e • linear p a b := by
  simp [linear, multiscalar_mul, smul_add, Finset.smul_sum, mul_smul]

@[simp] theorem linear_sub (p : Claim q A k) (a b c d : Vec k (ZMod q)) :
    linear p (a - c) (b - d) = linear p a b - linear p c d := by
  simp [linear, multiscalar_mul, sub_smul, Finset.sum_sub_distrib]; abel

theorem dot_expansion (s t a b : Vec k (ZMod q)) (e : ZMod q) :
    dot_product (s + e • a) (t + e • b) =
      dot_product s t + e * cross s t a b + e ^ 2 * dot_product a b := by
  simp only [dot_product, cross, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem honest_completeness (p : Claim q A k) (w : Witness q k)
    (hw : WitnessValid p w) (r : MaskRandomness q k) (e : ZMod q) :
    Verify p (honestTranscript p w r e) := by
  constructor
  · change linear p (r.1 + e • w.a) (r.2.1 + e • w.b) = _
    rw [linear_add, linear_smul, hw.1]
    rfl
  · change dot_product (r.1 + e • w.a) (r.2.1 + e • w.b) • p.generators.B +
      (r.2.2.1 + e * r.2.2.2 + e ^ 2 * w.rho) • p.generators.Hblind = _
    rw [dot_expansion, ← hw.2]
    simp only [honestTranscript, commit, add_smul, mul_smul, smul_add]
    abel

/-- The three challenges must be distinct; they may include zero. -/
def ValidFork (p : Claim q A k) (f : Fin 3 → Transcript q A k) : Prop :=
  (∀ i, Verify p (f i)) ∧
  (∀ i, (f i).announcement = (f 0).announcement) ∧
  Function.Injective (fun i => (f i).challenge)

def candidate (f : Fin 3 → Transcript q A k) : Witness q k :=
  ⟨((f 1).challenge - (f 0).challenge)⁻¹ • ((f 1).response.left - (f 0).response.left),
   ((f 1).challenge - (f 0).challenge)⁻¹ • ((f 1).response.right - (f 0).response.right),
   Interp.interpolate_quad (fun i => (f i).challenge) (fun i => (f i).response.blind) 2⟩

def candidateMasks (f : Fin 3 → Transcript q A k) : Vec k (ZMod q) × Vec k (ZMod q) :=
  ((f 0).response.left - (f 0).challenge • (candidate f).a,
   (f 0).response.right - (f 0).challenge • (candidate f).b)

def deviation (f : Fin 3 → Transcript q A k) : Vec k (ZMod q) × Vec k (ZMod q) :=
  ((f 2).response.left - ((candidateMasks f).1 + (f 2).challenge • (candidate f).a),
   (f 2).response.right - ((candidateMasks f).2 + (f 2).challenge • (candidate f).b))

def relation (d : Vec k (ZMod q) × Vec k (ZMod q)) : Range.RelationCoefficients q k :=
  ⟨d.1, d.2, 0, 0, 0⟩

inductive ExtractionResult (q k : ℕ) where
  | witness (w : Witness q k)
  | relation (d : Range.RelationCoefficients q k)
  deriving DecidableEq

def extract (f : Fin 3 → Transcript q A k) : ExtractionResult q k :=
  if deviation f = 0 then .witness (candidate f) else .relation (relation (deviation f))

def ResultValid (p : Claim q A k) : ExtractionResult q k → Prop
  | .witness w => WitnessValid p w
  | .relation d => d ≠ 0 ∧ Range.relation_eval p.generators d = 0

/-- Degree-two coefficient extraction works for arbitrary scalar modules. -/
theorem quadratic_module_top (x₀ x₁ x₂ : ZMod q) (a b c : A)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂)
    (h0 : a + x₀ • b + x₀ ^ 2 • c = 0)
    (h1 : a + x₁ • b + x₁ ^ 2 • c = 0)
    (h2 : a + x₂ • b + x₂ ^ 2 • c = 0) : c = 0 := by
  have ident :
      (((x₀ - x₁) * (x₀ - x₂))⁻¹) • (a + x₀ • b + x₀ ^ 2 • c) +
      (((x₁ - x₀) * (x₁ - x₂))⁻¹) • (a + x₁ • b + x₁ ^ 2 • c) +
      (((x₂ - x₀) * (x₂ - x₁))⁻¹) • (a + x₂ • b + x₂ ^ 2 • c) = c := by
    match_scalars <;> field_simp <;> ring
  simpa only [h0, h1, h2, smul_zero, add_zero] using ident.symm

theorem candidate_linear (p : Claim q A k) (f : Fin 3 → Transcript q A k)
    (hf : ValidFork p f) : linear p (candidate f).a (candidate f).b = p.P := by
  have hn : (f 1).challenge - (f 0).challenge ≠ 0 :=
    sub_ne_zero.mpr (hf.2.2.ne (by decide))
  change linear p (_ • _) (_ • _) = _
  rw [linear_smul, linear_sub, (hf.1 1).1, (hf.1 0).1, hf.2.1 1]
  simp only [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem masks_linear (p : Claim q A k) (f : Fin 3 → Transcript q A k)
    (hf : ValidFork p f) :
    linear p (candidateMasks f).1 (candidateMasks f).2 = (f 0).announcement.mask := by
  unfold candidateMasks
  rw [linear_sub, linear_smul, candidate_linear p f hf, (hf.1 0).1]
  exact add_sub_cancel_right _ _

theorem deviation_linear (p : Claim q A k) (f : Fin 3 → Transcript q A k)
    (hf : ValidFork p f) : linear p (deviation f).1 (deviation f).2 = 0 := by
  unfold deviation
  rw [linear_sub, linear_add, linear_smul, candidate_linear p f hf,
    masks_linear p f hf, (hf.1 2).1, hf.2.1 2, sub_self]

/-- Interpolated affine responses agree at the first two challenges. -/
theorem affine_second {X : Type} [AddCommGroup X] [Module (ZMod q) X]
    (x y : ZMod q) (u v : X) (h : y - x ≠ 0) :
    u - x • ((y - x)⁻¹ • (v - u)) + y • ((y - x)⁻¹ • (v - u)) = v := by
  calc
    _ = u + (y - x) • ((y - x)⁻¹ • (v - u)) := by rw [sub_smul]; abel
    _ = v := by rw [smul_smul, mul_inv_cancel₀ h, one_smul]; abel

omit [AddCommGroup A] [Module (ZMod q) A] in
theorem responses_affine (f : Fin 3 → Transcript q A k)
    (hx : Function.Injective (fun i => (f i).challenge)) (hd : deviation f = 0) (i : Fin 3) :
    (f i).response.left = (candidateMasks f).1 + (f i).challenge • (candidate f).a ∧
    (f i).response.right = (candidateMasks f).2 + (f i).challenge • (candidate f).b := by
  have hn : (f 1).challenge - (f 0).challenge ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  fin_cases i
  · simp [candidateMasks]
  · constructor <;> exact (affine_second _ _ _ _ hn).symm
  · exact ⟨sub_eq_zero.mp (congrArg Prod.fst hd), sub_eq_zero.mp (congrArg Prod.snd hd)⟩

theorem candidate_opening (p : Claim q A k) (f : Fin 3 → Transcript q A k)
    (hf : ValidFork p f) (hd : deviation f = 0) :
    dot_product (candidate f).a (candidate f).b • p.generators.B +
      (candidate f).rho • p.generators.Hblind = p.V := by
  let w := candidate f
  let s := (candidateMasks f).1
  let t := (candidateMasks f).2
  let coeff := Interp.interpolate_quad (fun i => (f i).challenge) (fun i => (f i).response.blind)
  let C0 := dot_product s t • p.generators.B + coeff 0 • p.generators.Hblind -
    (f 0).announcement.constant
  let C1 := cross s t w.a w.b • p.generators.B + coeff 1 • p.generators.Hblind -
    (f 0).announcement.slope
  let C2 := dot_product w.a w.b • p.generators.B + coeff 2 • p.generators.Hblind - p.V
  have hz (i : Fin 3) : C0 + (f i).challenge • C1 + (f i).challenge ^ 2 • C2 = 0 := by
    have hi := (hf.1 i).2
    rw [(responses_affine f hf.2.2 hd i).1, (responses_affine f hf.2.2 hd i).2,
      dot_expansion, hf.2.1 i] at hi
    have hc := Interp.interpolate_quad_evaluates (fun j => (f j).challenge)
      (fun j => (f j).response.blind) hf.2.2 i
    change coeff 0 + coeff 1 * (f i).challenge + coeff 2 * (f i).challenge ^ 2 = _ at hc
    rw [← hc] at hi
    dsimp [C0, C1, C2, s, t, w]
    simp only [add_smul, mul_smul, smul_sub, smul_add] at hi ⊢
    simp only [smul_smul, mul_comm (coeff 1), mul_comm (coeff 2)] at hi ⊢
    rw [← sub_eq_zero] at hi
    convert hi using 1; abel
  have hc := quadratic_module_top _ _ _ C0 C1 C2
    (hf.2.2.ne (by decide)) (hf.2.2.ne (by decide)) (hf.2.2.ne (by decide))
    (hz 0) (hz 1) (hz 2)
  exact sub_eq_zero.mp hc

theorem three_point_extraction_soundness (p : Claim q A k)
    (f : Fin 3 → Transcript q A k) (hf : ValidFork p f) : ResultValid p (extract f) := by
  unfold extract
  split_ifs with hd
  · exact ⟨candidate_linear p f hf, candidate_opening p f hf hd⟩
  · constructor
    · intro h
      apply hd
      exact Prod.ext (congrArg (fun d : Range.RelationCoefficients q k => d.g) h)
        (congrArg (fun d : Range.RelationCoefficients q k => d.h) h)
    · simpa [Range.relation_eval, CryptoBulletproofsRangeWitnessExtraction.relation_eval,
        relation, linear] using deviation_linear p f hf


abbrev SimulatorRandomness (q : ℕ) (A : Type) (k : ℕ) :=
  Vec k (ZMod q) × Vec k (ZMod q) × ZMod q × A

def simulateTranscript (p : Claim q A k) (e : ZMod q) (r : SimulatorRandomness q A k) :
    Transcript q A k :=
  ⟨⟨linear p r.1 r.2.1 - e • p.P,
    dot_product r.1 r.2.1 • p.generators.B + r.2.2.1 • p.generators.Hblind -
      e • r.2.2.2 - e ^ 2 • p.V, r.2.2.2⟩, e, ⟨r.1, r.2.1, r.2.2.1⟩⟩

theorem simulator_accepts (p : Claim q A k) (e : ZMod q) (r : SimulatorRandomness q A k) :
    Verify p (simulateTranscript p e r) := by
  constructor <;> dsimp [Verify, simulateTranscript] <;> abel

def toSimulatorRandomness (p : Claim q A k) (w : Witness q k) (e : ZMod q)
    (r : MaskRandomness q k) : SimulatorRandomness q A k :=
  ((respond w r e).left, (respond w r e).right, (respond w r e).blind, (commit p w r).slope)

theorem simulate_honest (p : Claim q A k) (w : Witness q k) (hw : WitnessValid p w)
    (r : MaskRandomness q k) (e : ZMod q) :
    simulateTranscript p e (toSimulatorRandomness p w e r) = honestTranscript p w r e := by
  have h := honest_completeness p w hw r e
  have hA := h.1
  have hT := h.2
  apply Transcript.ext
  · apply Announcement.ext
    · exact eq_sub_iff_add_eq.mpr hA.symm |>.symm
    · dsimp [Verify, honestTranscript] at hT
      dsimp [simulateTranscript, toSimulatorRandomness]
      rw [hT]
      abel
    · rfl
  · rfl
  · rfl

noncomputable def blinderEquiv (p : Claim q A k)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) : ZMod q ≃ A :=
  Equiv.ofBijective _ hb

@[simp] theorem blinderEquiv_apply (p : Claim q A k)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) (x : ZMod q) :
    blinderEquiv p hb x = x • p.generators.Hblind := rfl

@[simp] theorem blinder_inverse (p : Claim q A k)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) (x : ZMod q) :
    (blinderEquiv p hb).symm (x • p.generators.Hblind) = x :=
  (blinderEquiv p hb).symm_apply_apply x

@[simp] theorem blinder_inverse_smul (p : Claim q A k)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) (x : A) :
    (blinderEquiv p hb).symm x • p.generators.Hblind = x :=
  (blinderEquiv p hb).apply_symm_apply x

noncomputable def fromSimulatorRandomness (p : Claim q A k) (w : Witness q k) (e : ZMod q)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind))
    (r : SimulatorRandomness q A k) : MaskRandomness q k :=
  let s := r.1 - e • w.a
  let t := r.2.1 - e • w.b
  let tau := (blinderEquiv p hb).symm (r.2.2.2 - cross s t w.a w.b • p.generators.B)
  (s, t, r.2.2.1 - e * tau - e ^ 2 * w.rho, tau)

theorem randomness_left_inverse (p : Claim q A k) (w : Witness q k) (e : ZMod q)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) :
    Function.LeftInverse (fromSimulatorRandomness p w e hb) (toSimulatorRandomness p w e) := by
  rintro ⟨s, t, u, v⟩
  simp [fromSimulatorRandomness, toSimulatorRandomness, respond, commit]; ring

theorem randomness_right_inverse (p : Claim q A k) (w : Witness q k) (e : ZMod q)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) :
    Function.RightInverse (fromSimulatorRandomness p w e hb) (toSimulatorRandomness p w e) := by
  rintro ⟨l, m, z, T⟩
  simp [fromSimulatorRandomness, toSimulatorRandomness, respond, commit]; ring

noncomputable def hvzk_randomness_bijection (p : Claim q A k) (w : Witness q k) (e : ZMod q)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) :
    MaskRandomness q k ≃ SimulatorRandomness q A k where
  toFun := toSimulatorRandomness p w e
  invFun := fromSimulatorRandomness p w e hb
  left_inv := randomness_left_inverse p w e hb
  right_inv := randomness_right_inverse p w e hb

noncomputable def realView (p : Claim q A k) (w : Witness q k) (e : ZMod q) :
    PMF (Transcript q A k) :=
  (PMF.uniformOfFintype (MaskRandomness q k)).map (fun r => honestTranscript p w r e)

noncomputable def simView [Fintype A] (p : Claim q A k) (e : ZMod q) :
    PMF (Transcript q A k) :=
  (PMF.uniformOfFintype (SimulatorRandomness q A k)).map (simulateTranscript p e)

theorem real_view_eq_sim_view [Fintype A] (p : Claim q A k) (w : Witness q k)
    (hw : WitnessValid p w)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) (e : ZMod q) :
    realView p w e = simView p e := by
  have h := CryptoPedersenHomomorphicSum.map_uniform_equiv (hvzk_randomness_bijection p w e hb)
  unfold simView
  rw [← h, PMF.map_comp]
  change realView p w e = (PMF.uniformOfFintype (MaskRandomness q k)).map
    (fun r => simulateTranscript p e (toSimulatorRandomness p w e r))
  simp_rw [simulate_honest p w hw]
  rfl

/-- Real order is masks first, then an independent honest challenge. -/
noncomputable def honestInteraction (p : Claim q A k) (w : Witness q k) (nu : PMF (ZMod q)) :
    PMF (Transcript q A k) :=
  (PMF.uniformOfFintype (MaskRandomness q k)).bind fun r => nu.map (honestTranscript p w r)

noncomputable def simulatedInteraction [Fintype A] (p : Claim q A k) (nu : PMF (ZMod q)) :
    PMF (Transcript q A k) := nu.bind (simView p)

theorem interaction_hvzk [Fintype A] (p : Claim q A k) (w : Witness q k)
    (hw : WitnessValid p w)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) (nu : PMF (ZMod q)) :
    honestInteraction p w nu = simulatedInteraction p nu := by
  have horder : honestInteraction p w nu = nu.bind (realView p w) := PMF.bind_comm _ _ _
  rw [horder]
  unfold simulatedInteraction
  congr 1
  funext e
  exact real_view_eq_sim_view p w hw hb e


/-- Executable simulator: sample only field elements, never invert the blinding map. -/
def seededSimulator (p : Claim q A k) (e : ZMod q) (r : MaskRandomness q k) :
    Transcript q A k :=
  simulateTranscript p e (r.1, r.2.1, r.2.2.1, r.2.2.2 • p.generators.Hblind)

noncomputable def simulatorSeedEquiv (p : Claim q A k)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) :
    MaskRandomness q k ≃ SimulatorRandomness q A k :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.refl _) (blinderEquiv p hb)))

noncomputable def seededSimView (p : Claim q A k) (e : ZMod q) : PMF (Transcript q A k) :=
  (PMF.uniformOfFintype (MaskRandomness q k)).map (seededSimulator p e)

theorem seeded_sim_view_eq [Fintype A] (p : Claim q A k)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) (e : ZMod q) :
    seededSimView p e = simView p e := by
  have h := CryptoPedersenHomomorphicSum.map_uniform_equiv (simulatorSeedEquiv p hb)
  unfold simView
  rw [← h, PMF.map_comp]
  rfl

theorem real_view_eq_seeded_sim_view (p : Claim q A k) (w : Witness q k)
    (hw : WitnessValid p w)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind)) (e : ZMod q) :
    realView p w e = seededSimView p e := by
  let : Fintype A := Fintype.ofEquiv (ZMod q) (blinderEquiv p hb)
  exact (real_view_eq_sim_view p w hw hb e).trans (seeded_sim_view_eq p hb e).symm

instance [DecidableEq A] (p : Claim q A k) (f : Fin 3 → Transcript q A k) :
    Decidable (ValidFork p f) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def checkedExtract [DecidableEq A] (p : Claim q A k) (f : Fin 3 → Transcript q A k) :
    Option (ExtractionResult q k) := if ValidFork p f then some (extract f) else none

theorem checked_extract_success_iff [DecidableEq A] (p : Claim q A k)
    (f : Fin 3 → Transcript q A k) (r : ExtractionResult q k) :
    checkedExtract p f = some r ↔ ValidFork p f ∧ extract f = r := by
  simp only [checkedExtract]
  split_ifs <;> simp_all

theorem checked_extract_sound [DecidableEq A] (p : Claim q A k)
    (f : Fin 3 → Transcript q A k) (r : ExtractionResult q k)
    (h : checkedExtract p f = some r) : ResultValid p r := by
  obtain ⟨hf, hr⟩ := (checked_extract_success_iff p f r).mp h
  rw [← hr]
  exact three_point_extraction_soundness p f hf

def honestFork (p : Claim q A k) (w : Witness q k) (r : MaskRandomness q k)
    (x : Fin 3 → ZMod q) : Fin 3 → Transcript q A k := fun i => honestTranscript p w r (x i)

theorem honest_fork_valid (p : Claim q A k) (w : Witness q k) (hw : WitnessValid p w)
    (r : MaskRandomness q k) (x : Fin 3 → ZMod q) (hx : Function.Injective x) :
    ValidFork p (honestFork p w r x) :=
  ⟨fun i => honest_completeness p w hw r (x i), fun _ => rfl, hx⟩

theorem real_support (p : Claim q A k) (w : Witness q k) (e : ZMod q)
    (tr : Transcript q A k) : tr ∈ (realView p w e).support ↔
      ∃ r, honestTranscript p w r e = tr := by
  simp [realView]

/-- Registry exposes universal proofs; the hiding hypothesis is local to HVZK. -/
structure CryptoHiddenScalarInnerProductProtocolContractSuite : Prop where
  completeness : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (p : Claim q A k) (w : Witness q k), WitnessValid p w →
    ∀ (r : MaskRandomness q k) (e : ZMod q), Verify p (honestTranscript p w r e)
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (p : Claim q A k) (f : Fin 3 → Transcript q A k),
    ValidFork p f → ResultValid p (extract f)
  hvzk : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (p : Claim q A k) (w : Witness q k), WitnessValid p w →
    Function.Bijective (fun x : ZMod q => x • p.generators.Hblind) →
    ∀ e, realView p w e = seededSimView p e

theorem verification_suite : CryptoHiddenScalarInnerProductProtocolContractSuite where
  completeness := fun _ _ _ _ _ _ => honest_completeness
  extraction := fun _ _ _ _ _ _ => three_point_extraction_soundness
  hvzk := fun _ _ _ _ _ _ => real_view_eq_seeded_sim_view

end CryptoHiddenScalarInnerProductProtocolContract
