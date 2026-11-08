import Verification.ClaimTransportContract
open ClaimTransportContract

private def noise : Atom := ⟨"noise", "gamma < criticalGamma", "text-pin"⟩
private def domain : Atom := ⟨"domain", "0 <= F and F <= 1", "domain-pin"⟩
private def conclusion : Atom := ⟨"limit", "Tendsto orbit (nhds (1/4))", "limit-pin"⟩
private def anchor : Anchors := ⟨"coordinator-source", "coordinator-plan"⟩
private def source : Contract :=
  ⟨{noise, domain}, {conclusion}, {domain}, ∅, ∅, "fixed gamma",
    {⟨"limit", "F", "1/4", "dimensionless"⟩}, "hypothesis", ∅,
    {"No convergence rate"}, {"Kernel replay"}, "Selected quote"⟩

example : classify true anchor anchor none source source = .contractPreserved := by decide
example : exactContract source {source with premises := {domain, noise}} = true := by
  simp [exactContract, source, Finset.pair_comm]
example : classify true anchor anchor none source {source with premises := {domain}} =
    .reviewRequired := by decide
example : classify true anchor anchor none source
    {source with reportedEvidenceState := "formal_reported"} = .reviewRequired := by decide
example : classify true anchor anchor (some "Unaudited.theorem") source source =
    .reviewRequired := by decide
example : classify true anchor ⟨"candidate-chosen", "coordinator-plan"⟩ none source source =
    .invalidInput := by decide
example : classify false anchor anchor none source source = .invalidInput := by decide
example : exactContract source {source with quantities :=
    {⟨"limit", "F", "0.25", "dimensionless"⟩}} = false := by decide
example : exactContract source {source with openObligations := ∅} = false := by decide
example : ∀ s, (makeReport s).semanticEquivalenceVerified = false := by intro s; rfl

-- Omitting a premise need not preserve truth: a concrete logical countermodel.
example : (False → False) ∧ ¬ (True → False) := by simp
example (I : Atom → Prop) (a b a' b' : Finset Atom)
    (ha : a ⊆ a') (hb : b' ⊆ b) (h : Holds I a → Holds I b) :
    Holds I a' → Holds I b' := transport_of_inclusions I a b a' b' ha hb h
