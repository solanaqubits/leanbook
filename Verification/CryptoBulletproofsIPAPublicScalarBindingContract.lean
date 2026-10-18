/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsTreeExtraction

/-! Public scalar binding from two supplied accepting outer forks.
This is deterministic algebraic extraction, not a method of obtaining the forks. -/
namespace CryptoBulletproofsIPAPublicScalarBindingContract
open scoped BigOperators
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction

variable {q : ℕ} [Fact (Nat.Prime q)]
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A] {k : ℕ}

structure PublicClaim (q : ℕ) (A : Type) (k : ℕ) where
  U : A
  G : Vec k A
  H : Vec k A
  Q : A
  c : ZMod q
  deriving DecidableEq

def baseStatement (p : PublicClaim q A k) : Statement q A k :=
  ⟨p.U, p.G, p.H, p.Q⟩

def toIPA (p : PublicClaim q A k) (η : (ZMod q)ˣ) : Statement q A k :=
  ⟨(η : ZMod q) • p.U, p.G, p.H, p.Q + p.c • ((η : ZMod q) • p.U)⟩

def WitnessValid (p : PublicClaim q A k) (a b : Vec k (ZMod q)) : Prop :=
  p.Q = multiscalar_mul a p.G + multiscalar_mul b p.H ∧ dot_product a b = p.c

def ClaimResultValid (p : PublicClaim q A k) : TreeExtractionResult q k → Prop
  | .witness a b => WitnessValid p a b
  | .relation d => d ≠ 0 ∧ evaluate (baseStatement p) d = 0

instance [DecidableEq A] (p : PublicClaim q A k) (a b : Vec k (ZMod q)) :
    Decidable (WitnessValid p a b) := inferInstanceAs (Decidable (_ ∧ _))

instance [DecidableEq A] (p : PublicClaim q A k) (r : TreeExtractionResult q k) :
    Decidable (ClaimResultValid p r) := by
  cases r <;> unfold ClaimResultValid <;> infer_instance

/-- The coefficient of the scaled generator is transported to the original basis. -/
def liftRelation (η : (ZMod q)ˣ) (d : GeneratorCoefficients q k) :
    GeneratorCoefficients q k := (d.1, d.2.1, d.2.2 * (η : ZMod q))

theorem liftRelation_eval (p : PublicClaim q A k) (η : (ZMod q)ˣ)
    (d : GeneratorCoefficients q k) :
    evaluate (baseStatement p) (liftRelation η d) = evaluate (toIPA p η) d := by
  simp [evaluate, baseStatement, toIPA, liftRelation, smul_smul]

theorem liftRelation_injective (η : (ZMod q)ˣ) :
    Function.Injective (liftRelation (k := k) η) := by
  intro d e h
  have hg := congrArg (fun t : GeneratorCoefficients q k => t.1) h
  have hh := congrArg (fun t : GeneratorCoefficients q k => t.2.1) h
  have hu := congrArg (fun t : GeneratorCoefficients q k => t.2.2) h
  exact Prod.ext hg (Prod.ext hh (mul_right_cancel₀ (Units.ne_zero η) hu))

@[simp] theorem liftRelation_zero (η : (ZMod q)ˣ) :
    liftRelation (k := k) η 0 = 0 := by simp [liftRelation]

theorem liftRelation_nonzero (η : (ZMod q)ˣ) (d : GeneratorCoefficients q k)
    (hd : d ≠ 0) : liftRelation η d ≠ 0 := by
  intro h
  apply hd
  apply liftRelation_injective η
  simpa using h

/-- No independence assumption on G,H,U is used. -/
def difference (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (a₀ b₀ a₁ b₁ : Vec k (ZMod q)) : GeneratorCoefficients q k :=
  (a₀ - a₁, b₀ - b₁,
    (η₀ : ZMod q) * (dot_product a₀ b₀ - p.c) -
    (η₁ : ZMod q) * (dot_product a₁ b₁ - p.c))

theorem multiscalar_sub (a b : Vec k (ZMod q)) (G : Vec k A) :
    multiscalar_mul (a - b) G = multiscalar_mul a G - multiscalar_mul b G := by
  simp [multiscalar_mul, sub_smul, Finset.sum_sub_distrib]

theorem witness_equation (p : PublicClaim q A k) (η : (ZMod q)ˣ)
    (a b : Vec k (ZMod q))
    (h : ResultValid (toIPA p η) (.witness a b)) :
    p.Q = multiscalar_mul a p.G + multiscalar_mul b p.H +
      ((η : ZMod q) * (dot_product a b - p.c)) • p.U := by
  change p.Q + p.c • ((η : ZMod q) • p.U) =
    multiscalar_mul a p.G + multiscalar_mul b p.H +
      dot_product a b • ((η : ZMod q) • p.U) at h
  rw [← eq_sub_iff_add_eq] at h
  rw [h]
  simp only [sub_smul, mul_smul, mul_comm (η : ZMod q)]
  abel

theorem difference_eval (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (a₀ b₀ a₁ b₁ : Vec k (ZMod q))
    (h₀ : ResultValid (toIPA p η₀) (.witness a₀ b₀))
    (h₁ : ResultValid (toIPA p η₁) (.witness a₁ b₁)) :
    evaluate (baseStatement p) (difference p η₀ η₁ a₀ b₀ a₁ b₁) = 0 := by
  have h := (witness_equation p η₀ a₀ b₀ h₀).symm.trans
    (witness_equation p η₁ a₁ b₁ h₁)
  simp only [evaluate, baseStatement, difference, multiscalar_sub, sub_smul]
  calc
    _ = (multiscalar_mul a₀ p.G + multiscalar_mul b₀ p.H +
        ((η₀ : ZMod q) * (dot_product a₀ b₀ - p.c)) • p.U) -
        (multiscalar_mul a₁ p.G + multiscalar_mul b₁ p.H +
        ((η₁ : ZMod q) * (dot_product a₁ b₁ - p.c)) • p.U) := by abel
    _ = 0 := sub_eq_zero.mpr h

theorem difference_zero_witness (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (hne : η₀ ≠ η₁) (a₀ b₀ a₁ b₁ : Vec k (ZMod q))
    (h₀ : ResultValid (toIPA p η₀) (.witness a₀ b₀))
    (hd : difference p η₀ η₁ a₀ b₀ a₁ b₁ = 0) : WitnessValid p a₀ b₀ := by
  have ha : a₀ = a₁ := sub_eq_zero.mp (congrArg Prod.fst hd)
  have hb : b₀ = b₁ := sub_eq_zero.mp (congrArg (fun d => d.2.1) hd)
  have hu := congrArg (fun d : GeneratorCoefficients q k => d.2.2) hd
  simp only [difference, ha, hb, Prod.snd_zero] at hu
  have he : (η₀ : ZMod q) - η₁ ≠ 0 := sub_ne_zero.mpr (fun h => hne (Units.ext h))
  have hz : dot_product a₁ b₁ = p.c := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left he
    rw [sub_mul]
    exact hu
  constructor
  · rw [witness_equation p η₀ a₀ b₀ h₀, ha, hb, hz]
    simp
  · simpa only [ha, hb] using hz

/-- A relation branch takes priority; otherwise test the explicit difference vector. -/
def combineResults (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ) :
    TreeExtractionResult q k → TreeExtractionResult q k → TreeExtractionResult q k
  | .relation d, _ => .relation (liftRelation η₀ d)
  | .witness _ _, .relation d => .relation (liftRelation η₁ d)
  | .witness a₀ b₀, .witness a₁ b₁ =>
      let d := difference p η₀ η₁ a₀ b₀ a₁ b₁
      if d = 0 then .witness a₀ b₀ else .relation d

theorem combineResults_sound (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (hne : η₀ ≠ η₁) (r₀ r₁ : TreeExtractionResult q k)
    (h₀ : ResultValid (toIPA p η₀) r₀) (h₁ : ResultValid (toIPA p η₁) r₁) :
    ClaimResultValid p (combineResults p η₀ η₁ r₀ r₁) := by
  cases r₀ with
  | relation d => exact ⟨liftRelation_nonzero _ _ h₀.1, (liftRelation_eval p η₀ d).trans h₀.2⟩
  | witness a₀ b₀ =>
    cases r₁ with
    | relation d => exact ⟨liftRelation_nonzero _ _ h₁.1, (liftRelation_eval p η₁ d).trans h₁.2⟩
    | witness a₁ b₁ =>
      simp only [combineResults]
      split_ifs with hd
      · exact difference_zero_witness p η₀ η₁ hne a₀ b₀ a₁ b₁ h₀ hd
      · exact ⟨hd, difference_eval p η₀ η₁ a₀ b₀ a₁ b₁ h₀ h₁⟩

def extractPair (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (t₀ t₁ : IPATranscriptTree q A k) : TreeExtractionResult q k :=
  combineResults p η₀ η₁ (extractTree t₀) (extractTree t₁)

def ValidFork (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (t₀ t₁ : IPATranscriptTree q A k) : Prop :=
  η₀ ≠ η₁ ∧ ValidAcceptingTree (toIPA p η₀) t₀ ∧ ValidAcceptingTree (toIPA p η₁) t₁

instance [DecidableEq A] (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (t₀ t₁ : IPATranscriptTree q A k) : Decidable (ValidFork p η₀ η₁ t₀ t₁) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem pair_extraction_soundness (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (t₀ t₁ : IPATranscriptTree q A k) (h : ValidFork p η₀ η₁ t₀ t₁) :
    ClaimResultValid p (extractPair p η₀ η₁ t₀ t₁) :=
  combineResults_sound p η₀ η₁ h.1 _ _
    (tree_extraction_soundness _ _ h.2.1) (tree_extraction_soundness _ _ h.2.2)

def checkedPair [DecidableEq A] (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (t₀ t₁ : IPATranscriptTree q A k) : Except String (TreeExtractionResult q k) :=
  if ValidFork p η₀ η₁ t₀ t₁ then .ok (extractPair p η₀ η₁ t₀ t₁) else .error "invalidOuterFork"

theorem checkedPair_success_iff [DecidableEq A] (p : PublicClaim q A k)
    (η₀ η₁ : (ZMod q)ˣ) (t₀ t₁ : IPATranscriptTree q A k) :
    (checkedPair p η₀ η₁ t₀ t₁).isOk = true ↔ ValidFork p η₀ η₁ t₀ t₁ := by
  by_cases h : ValidFork p η₀ η₁ t₀ t₁ <;>
    simp [checkedPair, h, Except.isOk, Except.toBool]

theorem checkedPair_sound [DecidableEq A] (p : PublicClaim q A k)
    (η₀ η₁ : (ZMod q)ˣ) (t₀ t₁ : IPATranscriptTree q A k) (r : TreeExtractionResult q k)
    (h : checkedPair p η₀ η₁ t₀ t₁ = .ok r) : ClaimResultValid p r := by
  unfold checkedPair at h
  split_ifs at h with hv
  · cases h
    exact pair_extraction_soundness p η₀ η₁ t₀ t₁ hv

theorem checkedPair_diagonal [DecidableEq A] (p : PublicClaim q A k)
    (η : (ZMod q)ˣ) (t₀ t₁ : IPATranscriptTree q A k) :
    checkedPair p η η t₀ t₁ = .error "invalidOuterFork" := by
  simp [checkedPair, ValidFork]

/-- Context rejection is semantic: a tree must check at the computed statement. -/
theorem checkedPair_reject_left [DecidableEq A] (p : PublicClaim q A k)
    (η₀ η₁ : (ZMod q)ˣ) (t₀ t₁ : IPATranscriptTree q A k)
    (h : ¬ValidAcceptingTree (toIPA p η₀) t₀) :
    checkedPair p η₀ η₁ t₀ t₁ = .error "invalidOuterFork" := by
  simp [checkedPair, ValidFork, h]

theorem checkedPair_reject_right [DecidableEq A] (p : PublicClaim q A k)
    (η₀ η₁ : (ZMod q)ˣ) (t₀ t₁ : IPATranscriptTree q A k)
    (h : ¬ValidAcceptingTree (toIPA p η₁) t₁) :
    checkedPair p η₀ η₁ t₀ t₁ = .error "invalidOuterFork" := by
  simp [checkedPair, ValidFork, h]

/-- Honest public claims expose c separately from the vector commitment. -/
def honestClaim (U : A) (G H : Vec k A) (a b : Vec k (ZMod q)) : PublicClaim q A k :=
  ⟨U, G, H, multiscalar_mul a G + multiscalar_mul b H, dot_product a b⟩

@[simp] theorem honestClaim_toIPA (U : A) (G H : Vec k A) (a b : Vec k (ZMod q))
    (η : (ZMod q)ˣ) :
    toIPA (honestClaim U G H a b) η = witness_statement ((η : ZMod q) • U) G H a b := rfl

omit [AddCommGroup A] [Module (ZMod q) A] in
@[simp] theorem difference_same (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (a b : Vec k (ZMod q)) (hc : dot_product a b = p.c) :
    difference p η₀ η₁ a b a b = 0 := by simp [difference, hc]

theorem checkedPair_honest [DecidableEq A] (u : Fin 4 → (ZMod q)ˣ)
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (U : A) (G H : Vec k A) (a b : Vec k (ZMod q))
    (η₀ η₁ : (ZMod q)ˣ) (hne : η₀ ≠ η₁) :
    checkedPair (honestClaim U G H a b) η₀ η₁
      (honestTree u ((η₀ : ZMod q) • U) G H a b)
      (honestTree u ((η₁ : ZMod q) • U) G H a b) = .ok (.witness a b) := by
  have hv : ValidFork (honestClaim U G H a b) η₀ η₁
      (honestTree u ((η₀ : ZMod q) • U) G H a b)
      (honestTree u ((η₁ : ZMod q) • U) G H a b) :=
    ⟨hne, honestTree_valid u hd _ _ _ _ _, honestTree_valid u hd _ _ _ _ _⟩
  rw [checkedPair, if_pos hv]
  simp [extractPair, honestTree_exact u (hd.ne (by decide)), combineResults,
    difference, honestClaim]

namespace Counterexample
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
/-- At depth zero F5 suffices; it cannot supply four different nonzero squares. -/
def claim : PublicClaim 5 (ZMod 5) 0 := ⟨1, fun _ => 1, fun _ => 1, 4, 1⟩
def eta₀ : (ZMod 5)ˣ := 1
def eta₁ : (ZMod 5)ˣ := Units.mk0 (2 : ZMod 5) (by decide)
def first : IPATranscriptTree 5 (ZMod 5) 0 := .leaf (toIPA claim eta₀) 0 0
def second : IPATranscriptTree 5 (ZMod 5) 0 := .leaf (toIPA claim eta₁) 1 0
def relation : GeneratorCoefficients 5 0 := (fun _ => -1, fun _ => 0, 1)

theorem first_valid : ValidAcceptingTree (toIPA claim eta₀) first := by decide +kernel
theorem second_valid : ValidAcceptingTree (toIPA claim eta₁) second := by decide +kernel
theorem fork_valid : ValidFork claim eta₀ eta₁ first second := by decide +kernel

theorem no_public_witness : ¬∃ a b, WitnessValid claim a b := by decide +kernel

theorem single_tree_wrong_scalar :
    ResultValid (toIPA claim eta₀) (extractTree first) ∧
      ¬ClaimResultValid claim (extractTree first) := by decide +kernel

theorem diagonal_raw_wrong :
    extractPair claim eta₀ eta₀ first first = .witness 0 0 ∧
      ¬ClaimResultValid claim (extractPair claim eta₀ eta₀ first first) := by decide +kernel

theorem checked_relation : checkedPair claim eta₀ eta₁ first second = .ok (.relation relation) :=
  by decide +kernel

theorem explicit_relation : relation ≠ 0 ∧ evaluate (baseStatement claim) relation = 0 :=
  by decide +kernel
end Counterexample

structure CryptoBulletproofsIPAPublicScalarBindingContractSuite : Prop where
  lift : ∀ (q : ℕ) [Fact q.Prime] (k : ℕ) (η : (ZMod q)ˣ),
    Function.Injective (liftRelation (k := k) η)
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ) (t₀ t₁ : IPATranscriptTree q A k),
      ValidFork p η₀ η₁ t₀ t₁ → ClaimResultValid p (extractPair p η₀ η₁ t₀ t₁)
  checked : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (p : PublicClaim q A k) (η₀ η₁ : (ZMod q)ˣ)
    (t₀ t₁ : IPATranscriptTree q A k) (r : TreeExtractionResult q k),
      checkedPair p η₀ η₁ t₀ t₁ = .ok r → ClaimResultValid p r
  complete : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (u : Fin 4 → (ZMod q)ˣ),
    Function.Injective (fun i => (u i : ZMod q) ^ 2) →
    ∀ (U : A) (G H : Vec k A) (a b : Vec k (ZMod q)) (η₀ η₁ : (ZMod q)ˣ), η₀ ≠ η₁ →
    checkedPair (honestClaim U G H a b) η₀ η₁
      (honestTree u ((η₀ : ZMod q) • U) G H a b)
      (honestTree u ((η₁ : ZMod q) • U) G H a b) = .ok (.witness a b)
  countermodel : ValidFork Counterexample.claim Counterexample.eta₀ Counterexample.eta₁
    Counterexample.first Counterexample.second ∧ ¬∃ a b, WitnessValid Counterexample.claim a b

theorem verification_suite : CryptoBulletproofsIPAPublicScalarBindingContractSuite where
  lift := fun _ _ _ => liftRelation_injective
  extraction := fun _ _ _ _ _ _ => pair_extraction_soundness
  checked := fun _ _ _ _ _ _ _ => checkedPair_sound
  complete := fun _ _ _ _ _ _ _ => checkedPair_honest
  countermodel := ⟨Counterexample.fork_valid, Counterexample.no_public_witness⟩

end CryptoBulletproofsIPAPublicScalarBindingContract
