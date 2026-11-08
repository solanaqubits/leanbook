/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Finset.Basic

/-! Claim Transport 0.1: finite exact comparison and conditional logical transport.
The wire decoder, SHA-256, source extraction, Python implementation and interpretation
of natural language are outside this model. Finsets represent validated unique-ID lists.
Evidence states are reported strings, never assertions that evidence has been replayed. -/
namespace ClaimTransportContract
set_option autoImplicit false

structure Atom where
  id : String
  text : String
  digest : String
  deriving DecidableEq

structure Quantity where
  id : String
  symbol : String
  exactLiteral : String
  unit : String
  deriving DecidableEq

structure Contract where
  premises : Finset Atom
  conclusions : Finset Atom
  domains : Finset Atom
  quantifiers : Finset Atom
  negations : Finset Atom
  scope : String
  quantities : Finset Quantity
  reportedEvidenceState : String
  evidenceIds : Finset String
  nonClaims : Finset String
  openObligations : Finset String
  selectedQuote : String
  deriving DecidableEq

structure Anchors where
  sourceBundle : String
  plan : String
  deriving DecidableEq

inductive Status where
  | contractPreserved | reviewRequired | invalidInput
  deriving DecidableEq

/-- Executable finite comparison; list ordering is removed by the wire abstraction.
No comparison of meanings, arithmetic literals or proof references is performed. -/
def exactContract (source candidate : Contract) : Bool := decide (source = candidate)

/-- `wireValid` stands for the unproved decoder/binding checks. Expected anchors are
independent inputs, not selected by the candidate. Even a named Lean theorem is
an unverified reference here. -/
def classify (wireValid : Bool) (expected supplied : Anchors)
    (proofReference : Option String) (source candidate : Contract) : Status :=
  if wireValid = false ∨ expected ≠ supplied then .invalidInput
  else if proofReference.isSome ∨ exactContract source candidate = false then .reviewRequired
  else .contractPreserved

structure Report where
  status : Status
  semanticEquivalenceVerified : Bool
  sourceExtractionComplete : Bool
  kernelReplayed : Bool
  publicationAuthorized : Bool
  deriving DecidableEq

/-- All outcomes retain the same assurance boundary. -/
def makeReport (status : Status) : Report := ⟨status, false, false, false, false⟩

def Holds {α : Type} (I : α → Prop) (s : Finset α) : Prop := ∀ a ∈ s, I a

def Meaning (I : Atom → Prop) (c : Contract) : Prop :=
  Holds I c.premises → Holds I c.conclusions

theorem exactContract_iff (source candidate : Contract) :
    exactContract source candidate = true ↔ source = candidate := by
  simp [exactContract]

theorem classify_preserved_iff (valid : Bool) (e s : Anchors) (r : Option String)
    (a b : Contract) :
    classify valid e s r a b = .contractPreserved ↔
      valid = true ∧ e = s ∧ r = none ∧ a = b := by
  cases valid <;> cases r <;> by_cases he : e = s <;> by_cases hab : a = b <;>
    simp [classify, exactContract, he, hab]

theorem invalid_wire (e s : Anchors) (r : Option String) (a b : Contract) :
    classify false e s r a b = .invalidInput := by simp [classify]

theorem mismatched_anchors (valid : Bool) (e s : Anchors) (r : Option String)
    (a b : Contract) (h : e ≠ s) : classify valid e s r a b = .invalidInput := by
  simp [classify, h]

theorem proof_reference_requires_review (e : Anchors) (reference : String) (a b : Contract) :
    classify true e e (some reference) a b = .reviewRequired := by simp [classify]

theorem unequal_contract_requires_review (e : Anchors) (a b : Contract) (h : a ≠ b) :
    classify true e e none a b = .reviewRequired := by simp [classify, exactContract, h]

theorem accepted_fields_equal (valid : Bool) (e s : Anchors) (r : Option String)
    (a b : Contract) (h : classify valid e s r a b = .contractPreserved) :
    a.premises = b.premises ∧ a.conclusions = b.conclusions ∧ a.domains = b.domains ∧
    a.quantifiers = b.quantifiers ∧ a.negations = b.negations ∧ a.scope = b.scope ∧
    a.quantities = b.quantities ∧ a.reportedEvidenceState = b.reportedEvidenceState ∧
    a.evidenceIds = b.evidenceIds ∧ a.nonClaims = b.nonClaims ∧
    a.openObligations = b.openObligations ∧ a.selectedQuote = b.selectedQuote := by
  have hab := ((classify_preserved_iff valid e s r a b).mp h).2.2.2
  subst b
  simp

theorem holds_of_subset {α : Type} (I : α → Prop) (a b : Finset α)
    (h : a ⊆ b) (hb : Holds I b) : Holds I a := by
  intro x hx
  exact hb x (h hx)

/-- Strengthening premises and weakening conclusions transports an implication.
This theorem does not establish logical equivalence or non-vacuity. -/
theorem transport_of_inclusions {α : Type} (I : α → Prop) (a b a' b' : Finset α)
    (ha : a ⊆ a') (hb : b' ⊆ b) (source : Holds I a → Holds I b) :
    Holds I a' → Holds I b' := by
  intro candidatePremises
  exact holds_of_subset I b' b hb (source (holds_of_subset I a a' ha candidatePremises))

theorem implication_transport (a b a' b' : Prop)
    (premises : a' → a) (source : a → b) (conclusion : b → b') : a' → b' := by
  intro h
  exact conclusion (source (premises h))

theorem accepted_transport (I : Atom → Prop) (valid : Bool) (e s : Anchors)
    (r : Option String) (a b : Contract)
    (h : classify valid e s r a b = .contractPreserved) (source : Meaning I a) : Meaning I b := by
  have hab := ((classify_preserved_iff valid e s r a b).mp h).2.2.2
  simpa [← hab] using source

/-- Finset equality ignores ordering of a validated atom list. -/
theorem atom_order_irrelevant (xs ys : List Atom) (h : xs.Perm ys) :
    xs.toFinset = ys.toFinset := by
  ext a
  simp only [List.mem_toFinset]
  exact h.mem_iff

/-- Changing text under the same ID changes the atom; an ID alone is not its meaning. -/
theorem changed_text_changes_atom (a b : Atom) (h : a.text ≠ b.text) : a ≠ b := by
  intro he
  exact h (congrArg Atom.text he)

theorem removed_premise_not_exact (a b : Contract) (x : Atom)
    (ha : x ∈ a.premises) (hb : x ∉ b.premises) : exactContract a b = false := by
  have hne : a ≠ b := by
    intro he
    subst b
    exact hb ha
  simp [exactContract, hne]

theorem evidence_upgrade_not_exact (a b : Contract)
    (h : a.reportedEvidenceState ≠ b.reportedEvidenceState) : exactContract a b = false := by
  have hne : a ≠ b := fun he => h (congrArg Contract.reportedEvidenceState he)
  simp [exactContract, hne]

theorem report_assurances_false (s : Status) :
    (makeReport s).semanticEquivalenceVerified = false ∧
    (makeReport s).sourceExtractionComplete = false ∧
    (makeReport s).kernelReplayed = false ∧
    (makeReport s).publicationAuthorized = false := by simp [makeReport]

/-- Logical inclusion is deliberately broader than exact-contract acceptance. -/
theorem stronger_premise_is_not_equivalence :
    ((False → True) ∧ ¬ (True → False)) := by simp

structure ClaimTransportSuite : Prop where
  comparison : ∀ a b, exactContract a b = true ↔ a = b
  transport : ∀ (I : Atom → Prop) valid e s r a b,
    classify valid e s r a b = .contractPreserved → Meaning I a → Meaning I b
  no_status_promotion : ∀ s, (makeReport s).kernelReplayed = false ∧
    (makeReport s).publicationAuthorized = false

theorem verification_suite : ClaimTransportSuite :=
  ⟨exactContract_iff, accepted_transport, fun _ => ⟨rfl, rfl⟩⟩

end ClaimTransportContract
