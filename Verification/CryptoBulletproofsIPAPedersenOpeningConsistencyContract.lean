/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAPublicScalarBindingContract
import Verification.CryptoPedersenCommitmentOpeningExtractionContract

/-! Algebraic composition of SUPPLIED forks. The IPA contexts are checked after
extracting c from the opening fork. This is not a single-transcript hidden-c
verifier, a fork-acquisition algorithm, or a zero-knowledge theorem. -/
namespace CryptoBulletproofsIPAPedersenOpeningConsistencyContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
namespace Opening
export CryptoPedersenCommitmentOpeningExtractionContract
  (Transcript scalarMap ValidFork extractOpening honestTranscript honest_fork_valid
   honest_extracts scalar_soundness)
end Opening
namespace Public
export CryptoBulletproofsIPAPublicScalarBindingContract
  (PublicClaim baseStatement toIPA ValidFork extractPair ClaimResultValid
   pair_extraction_soundness checkedPair honestClaim checkedPair_honest)
end Public
namespace Range
export CryptoBulletproofsRangeWitnessExtraction (RelationCoefficients relation_eval)
export CryptoBulletproofsRangeReduction (Generators)
end Range
variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A] {k : ℕ}

/-- No scalar opening is included in the public input. -/
structure CommittedClaim (q : ℕ) (A : Type) (k : ℕ) where
  generators : Range.Generators q A k
  Q : A
  V : A

def publicClaim (p : CommittedClaim q A k) (c : ZMod q) : Public.PublicClaim q A k :=
  ⟨p.generators.U, p.generators.G, p.generators.H, p.Q, c⟩

structure ForkBundle (q : ℕ) (A : Type) (k : ℕ) where
  opening₀ : Opening.Transcript (ZMod q) (ZMod q × ZMod q) A
  opening₁ : Opening.Transcript (ZMod q) (ZMod q × ZMod q) A
  eta₀ : (ZMod q)ˣ
  eta₁ : (ZMod q)ˣ
  tree₀ : IPATranscriptTree q A k
  tree₁ : IPATranscriptTree q A k

def opening (f : ForkBundle q A k) : ZMod q × ZMod q :=
  Opening.extractOpening f.opening₀ f.opening₁

def OpeningValid (p : CommittedClaim q A k) (f : ForkBundle q A k) : Prop :=
  Opening.ValidFork (Opening.scalarMap p.generators.B p.generators.Hblind) p.V
    f.opening₀ f.opening₁

/-- Crucially, both trees use the scalar EXTRACTED from the same opening fork. -/
def ValidBundle (p : CommittedClaim q A k) (f : ForkBundle q A k) : Prop :=
  OpeningValid p f ∧ Public.ValidFork (publicClaim p (opening f).1)
    f.eta₀ f.eta₁ f.tree₀ f.tree₁

instance [DecidableEq A] (p : CommittedClaim q A k) (f : ForkBundle q A k) :
    Decidable (OpeningValid p f) := inferInstanceAs (Decidable (Opening.ValidFork _ _ _ _))
instance [DecidableEq A] (p : CommittedClaim q A k) (f : ForkBundle q A k) :
    Decidable (ValidBundle p f) := inferInstanceAs (Decidable (_ ∧ _))

structure BoundWitness (q k : ℕ) where
  a : Vec k (ZMod q)
  b : Vec k (ZMod q)
  c : ZMod q
  r : ZMod q
  deriving DecidableEq

def WitnessValid (p : CommittedClaim q A k) (w : BoundWitness q k) : Prop :=
  p.Q = multiscalar_mul w.a p.generators.G + multiscalar_mul w.b p.generators.H ∧
  dot_product w.a w.b = w.c ∧
  p.V = w.c • p.generators.B + w.r • p.generators.Hblind

inductive BundleResult (q k : ℕ) where
  | witness (w : BoundWitness q k)
  | relation (d : Range.RelationCoefficients q k)
  deriving DecidableEq

def ResultValid (p : CommittedClaim q A k) : BundleResult q k → Prop
  | .witness w => WitnessValid p w
  | .relation d => d ≠ 0 ∧ Range.relation_eval p.generators d = 0

instance [DecidableEq A] (p : CommittedClaim q A k) (w : BoundWitness q k) :
    Decidable (WitnessValid p w) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance [DecidableEq A] (p : CommittedClaim q A k) (r : BundleResult q k) :
    Decidable (ResultValid p r) := by
  cases r <;> unfold ResultValid <;> infer_instance

/-- Preserve the original G,H,U relation; do not invent Pedersen coefficients. -/
def liftRelation (d : GeneratorCoefficients q k) : Range.RelationCoefficients q k :=
  ⟨d.1, d.2.1, 0, 0, d.2.2⟩

theorem liftRelation_injective : Function.Injective (liftRelation (q := q) (k := k)) := by
  intro d e h
  exact Prod.ext (congrArg (fun t : Range.RelationCoefficients q k => t.g) h)
    (Prod.ext (congrArg (fun t : Range.RelationCoefficients q k => t.h) h)
      (congrArg (fun t : Range.RelationCoefficients q k => t.ipa) h))

@[simp] theorem liftRelation_zero : liftRelation (q := q) (k := k) 0 = 0 := rfl

theorem liftRelation_nonzero (d : GeneratorCoefficients q k) (hd : d ≠ 0) :
    liftRelation d ≠ 0 := by
  intro h
  exact hd (liftRelation_injective (h.trans liftRelation_zero.symm))

theorem liftRelation_eval (p : CommittedClaim q A k) (c : ZMod q)
    (d : GeneratorCoefficients q k) :
    Range.relation_eval p.generators (liftRelation d) =
      evaluate (Public.baseStatement (publicClaim p c)) d := by
  simp [Range.relation_eval, CryptoBulletproofsRangeWitnessExtraction.relation_eval,
    liftRelation, evaluate, Public.baseStatement, publicClaim]

def attachOpening (w : ZMod q × ZMod q) : TreeExtractionResult q k → BundleResult q k
  | .witness a b => .witness ⟨a, b, w.1, w.2⟩
  | .relation d => .relation (liftRelation d)

theorem attachOpening_sound (p : CommittedClaim q A k) (w : ZMod q × ZMod q)
    (hV : w.1 • p.generators.B + w.2 • p.generators.Hblind = p.V)
    (r : TreeExtractionResult q k) (hr : Public.ClaimResultValid (publicClaim p w.1) r) :
    ResultValid p (attachOpening w r) := by
  cases r with
  | witness a b => exact ⟨hr.1, hr.2, hV.symm⟩
  | relation d => exact ⟨liftRelation_nonzero d hr.1, (liftRelation_eval p w.1 d).trans hr.2⟩

def extractBundle (p : CommittedClaim q A k) (f : ForkBundle q A k) : BundleResult q k :=
  attachOpening (opening f) (Public.extractPair (publicClaim p (opening f).1)
    f.eta₀ f.eta₁ f.tree₀ f.tree₁)

theorem bundle_extraction_soundness (p : CommittedClaim q A k) (f : ForkBundle q A k)
    (h : ValidBundle p f) : ResultValid p (extractBundle p f) :=
  attachOpening_sound p (opening f)
    (Opening.scalar_soundness _ _ _ _ _ h.1) _
    (Public.pair_extraction_soundness _ _ _ _ _ h.2)

inductive BundleError where
  | invalidOpeningFork | invalidIPAFork
  deriving DecidableEq, Repr

/-- Check opening equations first, then IPA contexts at the extracted scalar. -/
def checkedBundle [DecidableEq A] (p : CommittedClaim q A k) (f : ForkBundle q A k) :
    Except BundleError (BundleResult q k) :=
  if OpeningValid p f then
    if Public.ValidFork (publicClaim p (opening f).1) f.eta₀ f.eta₁ f.tree₀ f.tree₁ then
      .ok (extractBundle p f)
    else .error .invalidIPAFork
  else .error .invalidOpeningFork

theorem checkedBundle_success_iff [DecidableEq A] (p : CommittedClaim q A k)
    (f : ForkBundle q A k) (r : BundleResult q k) :
    checkedBundle p f = .ok r ↔ ValidBundle p f ∧ extractBundle p f = r := by
  simp only [checkedBundle, ValidBundle]
  split_ifs <;> simp_all

theorem checkedBundle_sound [DecidableEq A] (p : CommittedClaim q A k)
    (f : ForkBundle q A k) (r : BundleResult q k) (h : checkedBundle p f = .ok r) :
    ResultValid p r := by
  obtain ⟨hv, he⟩ := (checkedBundle_success_iff p f r).mp h
  rw [← he]
  exact bundle_extraction_soundness p f hv

theorem checkedBundle_reject_opening [DecidableEq A] (p : CommittedClaim q A k)
    (f : ForkBundle q A k) (h : ¬OpeningValid p f) :
    checkedBundle p f = .error .invalidOpeningFork := by simp [checkedBundle, h]

theorem checkedBundle_reject_context [DecidableEq A] (p : CommittedClaim q A k)
    (f : ForkBundle q A k) (hv : OpeningValid p f)
    (hi : ¬Public.ValidFork (publicClaim p (opening f).1) f.eta₀ f.eta₁ f.tree₀ f.tree₁) :
    checkedBundle p f = .error .invalidIPAFork := by simp [checkedBundle, hv, hi]

/-- Honest constructor is only for completeness, not an assumption in extraction. -/
def honestClaim (g : Range.Generators q A k) (a b : Vec k (ZMod q)) (r : ZMod q) :
    CommittedClaim q A k :=
  ⟨g, multiscalar_mul a g.G + multiscalar_mul b g.H, dot_product a b • g.B + r • g.Hblind⟩

def honestBundle (g : Range.Generators q A k) (a b : Vec k (ZMod q)) (r : ZMod q)
    (mask : ZMod q × ZMod q) (e₀ e₁ : ZMod q) (η₀ η₁ : (ZMod q)ˣ)
    (u : Fin 4 → (ZMod q)ˣ) : ForkBundle q A k :=
  ⟨Opening.honestTranscript (Opening.scalarMap g.B g.Hblind) (dot_product a b, r) mask e₀,
   Opening.honestTranscript (Opening.scalarMap g.B g.Hblind) (dot_product a b, r) mask e₁,
   η₀, η₁, honestTree u ((η₀ : ZMod q) • g.U) g.G g.H a b,
   honestTree u ((η₁ : ZMod q) • g.U) g.G g.H a b⟩

theorem honest_opening (g : Range.Generators q A k) (a b : Vec k (ZMod q)) (r : ZMod q)
    (mask : ZMod q × ZMod q) (e₀ e₁ : ZMod q) (he : e₀ ≠ e₁)
    (η₀ η₁ : (ZMod q)ˣ) (u : Fin 4 → (ZMod q)ˣ) :
    opening (honestBundle g a b r mask e₀ e₁ η₀ η₁ u) = (dot_product a b, r) :=
  Opening.honest_extracts _ _ _ _ _ he

theorem honest_bundle_valid (g : Range.Generators q A k) (a b : Vec k (ZMod q)) (r : ZMod q)
    (mask : ZMod q × ZMod q) (e₀ e₁ : ZMod q) (he : e₀ ≠ e₁)
    (η₀ η₁ : (ZMod q)ˣ) (hη : η₀ ≠ η₁) (u : Fin 4 → (ZMod q)ˣ)
    (hu : Function.Injective (fun i => (u i : ZMod q) ^ 2)) :
    ValidBundle (honestClaim g a b r) (honestBundle g a b r mask e₀ e₁ η₀ η₁ u) := by
  constructor
  · exact Opening.honest_fork_valid _ _ _ _ _ he
  · rw [honest_opening g a b r mask e₀ e₁ he]
    exact ⟨hη, honestTree_valid u hu _ _ _ _ _, honestTree_valid u hu _ _ _ _ _⟩

theorem checkedBundle_honest [DecidableEq A] (g : Range.Generators q A k)
    (a b : Vec k (ZMod q)) (r : ZMod q) (mask : ZMod q × ZMod q)
    (e₀ e₁ : ZMod q) (he : e₀ ≠ e₁) (η₀ η₁ : (ZMod q)ˣ) (hη : η₀ ≠ η₁)
    (u : Fin 4 → (ZMod q)ˣ) (hu : Function.Injective (fun i => (u i : ZMod q) ^ 2)) :
    checkedBundle (honestClaim g a b r) (honestBundle g a b r mask e₀ e₁ η₀ η₁ u) =
      .ok (.witness ⟨a, b, dot_product a b, r⟩) := by
  apply (checkedBundle_success_iff _ _ _).mpr
  refine ⟨honest_bundle_valid g a b r mask e₀ e₁ he η₀ η₁ hη u hu, ?_⟩
  unfold extractBundle
  rw [honest_opening g a b r mask e₀ e₁ he]
  simp [Public.extractPair, honestBundle, honestTree_exact u (hu.ne (by decide)),
    CryptoBulletproofsIPAPublicScalarBindingContract.combineResults,
    CryptoBulletproofsIPAPublicScalarBindingContract.difference, publicClaim,
    honestClaim, attachOpening]

structure CryptoBulletproofsIPAPedersenOpeningConsistencyContractSuite : Prop where
  lift : ∀ (q : ℕ) [Fact q.Prime] (k : ℕ),
    Function.Injective (liftRelation (q := q) (k := k))
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (p : CommittedClaim q A k) (f : ForkBundle q A k),
    ValidBundle p f → ResultValid p (extractBundle p f)
  complete : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (g : Range.Generators q A k) (a b : Vec k (ZMod q))
    (r : ZMod q) (mask : ZMod q × ZMod q) (e₀ e₁ : ZMod q), e₀ ≠ e₁ →
    ∀ (η₀ η₁ : (ZMod q)ˣ), η₀ ≠ η₁ → ∀ (u : Fin 4 → (ZMod q)ˣ),
    Function.Injective (fun i => (u i : ZMod q) ^ 2) →
    checkedBundle (honestClaim g a b r) (honestBundle g a b r mask e₀ e₁ η₀ η₁ u) =
      .ok (.witness ⟨a, b, dot_product a b, r⟩)
  checked : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (p : CommittedClaim q A k) (f : ForkBundle q A k)
    (r : BundleResult q k),
    checkedBundle p f = .ok r → ResultValid p r

theorem verification_suite : CryptoBulletproofsIPAPedersenOpeningConsistencyContractSuite where
  lift := fun _ _ _ => liftRelation_injective
  extraction := fun _ _ _ _ _ _ => bundle_extraction_soundness
  complete := fun _ _ _ _ _ _ _ => checkedBundle_honest
  checked := fun _ _ _ _ _ _ _ => checkedBundle_sound

end CryptoBulletproofsIPAPedersenOpeningConsistencyContract
