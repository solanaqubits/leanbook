/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarForkRecursiveQuotaContract

/-! Single causal execution on one adversary tape. Raw execution collects a
syntactically complete path; local check failure sets acceptance to false.
Primitive abort/malformed packets produce no transcript. No fork acquisition,
quota inference, random-oracle or complexity claim. -/
namespace CryptoHiddenScalarSinglePathContract
open CryptoHiddenScalarForkAcquisitionContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
open CryptoHiddenScalarForkRecursiveQuotaContract
namespace Comp
export CryptoHiddenScalarInnerProductCompressionContract
  (CompressedTranscript compressedVerify scalarCheck responseClaim)
end Comp
namespace Heavy
export CryptoBulletproofsIPAFiniteForkingProbabilityContract
  (average heavy heavyFraction heavy_prefix_fraction_lower)
end Heavy
namespace Avg
export CryptoHiddenScalarForkLocalDensityContract
  (average product_event_average)
end Avg

/-- One seed per interactive challenge, not one block per acquisition retry. -/
def PathSeed {q : ℕ} {S : Type} : {d : ℕ} → TreePlan q S d → Type
  | _, .leaf => Unit
  | _, .node law _ child => Fin law.size × PathSeed child
instance {q : ℕ} {S : Type} : {d : ℕ} → (p : TreePlan q S d) → Fintype (PathSeed p)
  | _, .leaf => inferInstanceAs (Fintype Unit)
  | _, .node law _ child => letI := instFintypePathSeed child
                           inferInstanceAs (Fintype (Fin law.size × PathSeed child))
instance {q : ℕ} {S : Type} : {d : ℕ} → (p : TreePlan q S d) → DecidableEq (PathSeed p)
  | _, .leaf => inferInstanceAs (DecidableEq Unit)
  | _, .node law _ child => letI := instDecidableEqPathSeed child
                           inferInstanceAs (DecidableEq (Fin law.size × PathSeed child))

variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
  [DecidableEq A] {Ω S : Type} {k : ℕ}

/-- All nodes, including the terminal snapshot, are reachable. Transitions carry
real equations for this model, this tape and this exact prefix. -/
def IPAPathProvenance (m : AdversaryModel q A Ω S) : {d : ℕ} → Snapshot q S →
    Packet q A → (Fin d → (ZMod q)ˣ) → IPATranscript q A d → Prop
  | 0, s, msg, _, tr => ReachableSnapshot m s ∧ msg = .leaf tr.a_final tr.b_final
  | d+1, s, msg, xs, tr => ReachableSnapshot m s ∧ msg = .round (tr.rounds 0) ∧
      ∃ o : Observation m s (.inner d (xs 0)),
        IPAPathProvenance m o.after o.packet (Fin.tail xs) (transcript_tail tr)

structure IPAResult (q : ℕ) (A : Type) (d : ℕ) where
  challenges : Fin d → (ZMod q)ˣ
  proof : IPATranscript q A d
  accepted : Bool

abbrev CertifiedIPA (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (msg : Packet q A) (st : Statement q A k) :=
  {r : IPAResult q A k // IPAPathProvenance m s msg r.challenges r.proof ∧
    r.accepted = verifier st.U st.G st.H st.P r.challenges r.proof}

/-- Messages are obtained before choosing their following challenge. The final
check is propagated through the actual folded contexts, not a supplied witness. -/
def runIPA (m : AdversaryModel q A Ω S) : {d : ℕ} → (p : TreePlan q S d) →
    (s : Snapshot q S) → ReachableSnapshot m s → (msg : Packet q A) →
    (st : Statement q A d) → PathSeed p → Option (CertifiedIPA m s msg st)
  | 0, .leaf, _s, hs, msg, st, _ => match msg with
    | .leaf a b => some ⟨⟨Fin.elim0, ⟨Fin.elim0,a,b⟩,
        decide (st.P = a • st.G 0 + b • st.H 0 + (a*b) • st.U)⟩,
        ⟨⟨hs,rfl⟩,rfl⟩⟩
    | _ => none
  | d+1, .node law _ child, s, hs, msg, st, seed => match msg with
    | .round lr =>
      let x := law.call s seed.1
      match query m s (.inner d x) with
      | none => none
      | some o => match runIPA m child o.after (o.reachable hs) o.packet
          (child_statement st lr x) seed.2 with
        | none => none
        | some tail => some ⟨⟨Fin.cons x tail.val.challenges,
            ⟨Fin.cons lr tail.val.proof.rounds,tail.val.proof.a_final,tail.val.proof.b_final⟩,
            tail.val.accepted⟩,
            ⟨⟨hs,rfl,o,tail.property.1⟩,tail.property.2⟩⟩
    | _ => none

def SinglePathProvenance (m : AdversaryModel q A Ω S)
    (tr : Comp.CompressedTranscript q A k) : Prop :=
  ∃ c : Observation m (initialSnapshot m) .commit,
    c.packet = .announcement tr.announcement ∧
    ∃ e : Observation m c.after (.outer tr.challenge),
      e.packet = .scalar tr.product tr.blind ∧
      ∃ b : Observation m e.after (.binding tr.eta),
        ReachableSnapshot m c.after ∧ ReachableSnapshot m e.after ∧
        IPAPathProvenance m b.after b.packet tr.rounds tr.proof

omit [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A] in
/-- Observations of the same restored state/request cannot change their packet,
internal memory or tape consumption. -/
theorem observation_unique (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (req : Request q) (a b : Observation m s req) : a = b := by
  cases a with
  | mk pa ma ua ha =>
    cases b with
    | mk pb mb ub hb =>
      have h := Option.some.inj (ha.symm.trans hb)
      cases h
      rfl

omit [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A] in
/-- Even different future challenges cannot change the committed announcement. -/
theorem announcement_prefix (m : AdversaryModel q A Ω S)
    (a b : Comp.CompressedTranscript q A k)
    (ha : SinglePathProvenance m a) (hb : SinglePathProvenance m b) :
    a.announcement = b.announcement := by
  obtain ⟨oa,ha,_⟩ := ha
  obtain ⟨ob,hb,_⟩ := hb
  have h := observation_unique m _ _ oa ob
  subst ob
  exact Packet.announcement.inj (ha.symm.trans hb)

omit [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A] in
/-- The scalar response is fixed before eta and all inner calls. -/
theorem scalar_prefix (m : AdversaryModel q A Ω S)
    (a b : Comp.CompressedTranscript q A k)
    (ha : SinglePathProvenance m a) (hb : SinglePathProvenance m b)
    (he : a.challenge = b.challenge) : a.product = b.product ∧ a.blind = b.blind := by
  obtain ⟨ca,_,ea,ha,_⟩ := ha
  obtain ⟨cb,_,eb,hb,_⟩ := hb
  have hc := observation_unique m _ _ ca cb
  subst cb
  cases a with
  | mk ann e t z eta xs proof =>
    cases b with
    | mk ann' e' t' z' eta' xs' proof' =>
      dsimp at he
      subst e'
      have ho := observation_unique m _ _ ea eb
      subst eb
      exact Packet.scalar.inj (ha.symm.trans hb)

structure PathResult (q : ℕ) (A : Type) (k : ℕ) where
  transcript : Comp.CompressedTranscript q A k
  accepted : Bool

abbrev CertifiedPath (claim : F.Claim q A k) (m : AdversaryModel q A Ω S) :=
  {r : PathResult q A k // SinglePathProvenance m r.transcript ∧
    (r.accepted = true ↔ Comp.compressedVerify claim r.transcript)}

abbrev SinglePathSeed (p : ProtocolPlan q S k) :=
  Fin p.law.size × Fin p.eta.law.size × PathSeed p.eta.tree

/-- Primitive abort and wrong packet shapes yield none. Scalar/leaf check
failures remain observable as a complete rejected transcript when syntax permits. -/
def executeCertified (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p) : Option (CertifiedPath claim m) := do
  let c ← query m (initialSnapshot m) .commit
  match hc : c.packet with
  | .announcement ann =>
    let e := p.law.call c.after seed.1
    let o ← query m c.after (.outer e)
    match he : o.packet with
    | .scalar t z =>
      let eta := p.eta.law.call o.after seed.2.1
      let b ← query m o.after (.binding eta)
      let ip ← runIPA m p.eta.tree b.after (b.reachable (o.reachable (c.reachable .initial)))
        b.packet (P.toIPA (Comp.responseClaim claim ann e t) eta) seed.2.2
      let tr : Comp.CompressedTranscript q A k := ⟨ann,e,t,z,eta,ip.val.challenges,ip.val.proof⟩
      let ok := decide (Comp.scalarCheck claim ann e t z) && ip.val.accepted
      have hp : SinglePathProvenance m tr :=
        ⟨c,hc,o,he,b,c.reachable .initial,o.reachable (c.reachable .initial),ip.property.1⟩
      have hv : ok = true ↔ Comp.compressedVerify claim tr := by
        simp only [ok, Bool.and_eq_true, decide_eq_true_eq, ip.property.2]
        rfl
      pure ⟨⟨tr,ok⟩,hp,hv⟩
    | _ => none
  | _ => none

/-- Proof fields are erased; no accepting transcript is an input. -/
def execute (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p) : Option (PathResult q A k) :=
  (executeCertified p claim m seed).map Subtype.val

def ProducedTranscript (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p)
    (tr : Comp.CompressedTranscript q A k) : Prop :=
  ∃ r, execute p claim m seed = some r ∧ r.transcript = tr

def AcceptedRun (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p) : Prop :=
  ∃ r, execute p claim m seed = some r ∧ r.accepted = true

instance (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p) :
    Decidable (AcceptedRun p claim m seed) :=
  decidable_of_iff ((execute p claim m seed).any (fun r => r.accepted) = true)
    (by simp [AcceptedRun, Option.any_eq_true])

theorem execute_properties (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p) (r : PathResult q A k)
    (h : execute p claim m seed = some r) :
    SinglePathProvenance m r.transcript ∧
      (r.accepted = true ↔ Comp.compressedVerify claim r.transcript) := by
  unfold execute at h
  cases he : executeCertified p claim m seed with
  | none => simp [he] at h
  | some v => simp only [he,Option.map_some,Option.some.injEq] at h; subst r; exact v.property

theorem produced_provenance (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p) (tr : Comp.CompressedTranscript q A k)
    (h : ProducedTranscript p claim m seed tr) : SinglePathProvenance m tr := by
  obtain ⟨r,hr,rfl⟩ := h
  exact (execute_properties p claim m seed r hr).1

theorem accepted_iff_verifies (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p) :
    AcceptedRun p claim m seed ↔ ∃ tr, ProducedTranscript p claim m seed tr ∧
      Comp.compressedVerify claim tr := by
  constructor
  · rintro ⟨r,hr,ha⟩
    exact ⟨r.transcript,⟨r,hr,rfl⟩,(execute_properties p claim m seed r hr).2.mp ha⟩
  · rintro ⟨tr,⟨r,hr,rfl⟩,hv⟩
    exact ⟨r,hr,(execute_properties p claim m seed r hr).2.mpr hv⟩

theorem none_not_accepted (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p)
    (h : execute p claim m seed = none) : ¬ AcceptedRun p claim m seed := by
  simp [AcceptedRun,h]

/-- A concrete cut at any IPA challenge boundary. -/
inductive TreeCut : {d : ℕ} → TreePlan q S d → Type where
  | here (p : TreePlan q S d) : TreeCut p
  | next (law : CallLaw (Snapshot q S) (ZMod q)ˣ (ZMod q) (fun x => (x : ZMod q)^2))
      (T : ℕ) (child : TreePlan q S d) (cut : TreeCut child) : TreeCut (.node law T child)
namespace TreeCut

def Prefix : {d : ℕ} → {p : TreePlan q S d} → TreeCut p → Type
  | _, _, .here _ => Unit
  | _, _, .next law _ _ cut => Fin law.size × Prefix cut

def Suffix : {d : ℕ} → {p : TreePlan q S d} → TreeCut p → Type
  | _, _, .here p => PathSeed p
  | _, _, .next _ _ _ cut => Suffix cut

instance : {d : ℕ} → {p : TreePlan q S d} → (c : TreeCut p) → Fintype c.Prefix
  | _, _, .here _ => inferInstanceAs (Fintype Unit)
  | _, _, .next law _ _ cut => letI := instFintypePrefix cut
                              inferInstanceAs (Fintype (Fin law.size × Prefix cut))
instance : {d : ℕ} → {p : TreePlan q S d} → (c : TreeCut p) → Fintype c.Suffix
  | _, _, .here p => inferInstanceAs (Fintype (PathSeed p))
  | _, _, .next _ _ _ cut => instFintypeSuffix cut

instance : {d : ℕ} → {p : TreePlan q S d} → (c : TreeCut p) → DecidableEq c.Prefix
  | _, _, .here _ => inferInstanceAs (DecidableEq Unit)
  | _, _, .next law _ _ cut => letI := instDecidableEqPrefix cut
                              inferInstanceAs (DecidableEq (Fin law.size × Prefix cut))
instance : {d : ℕ} → {p : TreePlan q S d} → (c : TreeCut p) → DecidableEq c.Suffix
  | _, _, .here p => inferInstanceAs (DecidableEq (PathSeed p))
  | _, _, .next _ _ _ cut => instDecidableEqSuffix cut

/-- Splitting preserves every seed occurrence, never quotients by decoded calls. -/
def split : {d : ℕ} → {p : TreePlan q S d} → (c : TreeCut p) →
    PathSeed p ≃ c.Prefix × c.Suffix
  | _, _, .here _ => ⟨fun w => ((),w), Prod.snd, fun _ => rfl, fun ⟨(),_⟩ => rfl⟩
  | _, _, .next law _ _ cut =>
      (Equiv.prodCongr (Equiv.refl (Fin law.size)) cut.split).trans
        (Equiv.prodAssoc _ _ _).symm
end TreeCut

/-- Prefix after e; eta and IPA are still fresh. -/
def afterESplit (p : ProtocolPlan q S k) :
    SinglePathSeed p ≃ Fin p.law.size × (Fin p.eta.law.size × PathSeed p.eta.tree) := Equiv.refl _

/-- Prefix after eta and any selected number of inner challenges. -/
def afterRoundSplit (p : ProtocolPlan q S k) (c : TreeCut p.eta.tree) :
    SinglePathSeed p ≃
      ((Fin p.law.size × Fin p.eta.law.size) × c.Prefix) × c.Suffix :=
  ((Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr (Equiv.refl _) c.split)).trans (Equiv.prodAssoc _ _ _).symm

section FinitePrefixes
variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]

def acceptanceRate (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) : ℚ :=
  Prob.probability (Finset.univ : Finset (SinglePathSeed p))
    (Finset.univ.filter fun w => AcceptedRun p claim m w)

/-- No conditioning on an accepting prefix. Invalid prefixes retain zero rows;
all microseed occurrences remain in the denominator. -/
def continuationRate (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (cut : SinglePathSeed p ≃ X × Y) (x : X) : ℚ :=
  Prob.probability (Finset.univ : Finset Y)
    (Finset.univ.filter fun y => AcceptedRun p claim m (cut.symm (x,y)))

theorem acceptance_eq_prefix_average (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (cut : SinglePathSeed p ≃ X × Y) :
    acceptanceRate p claim m = Heavy.average Finset.univ (continuationRate p claim m cut) := by
  classical
  have hc : (Finset.univ.filter fun w => AcceptedRun p claim m w).card =
      (Finset.univ.filter fun z : X × Y => AcceptedRun p claim m (cut.symm z)).card := by
    apply Finset.card_bij (fun w _ => cut w)
    · intro w hw
      simpa using hw
    · intro a _ b _ h; exact cut.injective h
    · intro z hz
      exact ⟨cut.symm z, by simpa using hz, cut.apply_symm_apply z⟩
  have he := Avg.product_event_average (Finset.univ : Finset X) (Finset.univ : Finset Y)
    (fun x y => decide (AcceptedRun p claim m (cut.symm (x,y))))
  simpa only [Finset.univ_product_univ, decide_eq_true_eq, acceptanceRate,
    continuationRate, Prob.probability, Finset.univ_inter, Finset.inter_univ, Finset.card_univ,
    Fintype.card_congr cut, hc, Heavy.average, Avg.average] using he

omit [Fintype X] in
theorem continuation_range (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (cut : SinglePathSeed p ≃ X × Y) (x : X) :
    0 ≤ continuationRate p claim m cut x ∧ continuationRate p claim m cut x ≤ 1 := by
  constructor
  · exact CryptoBulletproofsIPATreeProbabilityContract.probability_nonnegative _ _
  · by_cases h : (Finset.univ : Finset Y).Nonempty
    · exact CryptoBulletproofsIPATreeProbabilityContract.probability_le_one _ _ h
    · simp [continuationRate, Prob.probability, Finset.not_nonempty_iff_eq_empty.mp h]

theorem heavy_prefix_lower [Nonempty X] (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (cut : SinglePathSeed p ≃ X × Y)
    (theta : ℚ) (ht : theta < 1) :
    max 0 ((acceptanceRate p claim m - theta)/(1-theta)) ≤
      Heavy.heavyFraction Finset.univ (continuationRate p claim m cut) theta := by
  apply max_le
  · unfold Heavy.heavyFraction; positivity
  · rw [acceptance_eq_prefix_average p claim m cut]
    exact Heavy.heavy_prefix_fraction_lower _ Finset.univ_nonempty _ theta ht
      (fun x _ => (continuation_range p claim m cut x).2)

omit [Fintype X] in
/-- Positive heavy rows contain a real accepting continuation with provenance;
they do not assert that all continuations or all reachable snapshots accept. -/
theorem heavy_prefix_has_execution (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (cut : SinglePathSeed p ≃ X × Y)
    (x : X) (theta : ℚ) (ht : 0 < theta)
    (hx : theta ≤ continuationRate p claim m cut x) :
    ∃ y tr, ProducedTranscript p claim m (cut.symm (x,y)) tr ∧
      SinglePathProvenance m tr ∧ Comp.compressedVerify claim tr := by
  have hp : 0 < continuationRate p claim m cut x := ht.trans_le hx
  have hn : (Finset.univ.filter fun y => AcceptedRun p claim m (cut.symm (x,y))).Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty] at h
    simp [continuationRate,h,Prob.probability] at hp
  obtain ⟨y,hy⟩ := hn
  obtain ⟨tr,htr,hv⟩ := (accepted_iff_verifies p claim m _).mp (Finset.mem_filter.mp hy).2
  exact ⟨y,tr,htr,produced_provenance p claim m _ tr htr,hv⟩
end FinitePrefixes

structure CryptoHiddenScalarSinglePathContractSuite : Prop where
  equivalence : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S : Type) (k : ℕ) (p : ProtocolPlan q S k)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p),
    AcceptedRun p claim m seed ↔ ∃ tr, ProducedTranscript p claim m seed tr ∧
      Comp.compressedVerify claim tr
  provenance : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S : Type) (k : ℕ) (p : ProtocolPlan q S k)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S) (seed : SinglePathSeed p)
    (tr : Comp.CompressedTranscript q A k), ProducedTranscript p claim m seed tr →
      SinglePathProvenance m tr
  heavy_prefix : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S X Y : Type)
    [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X]
    (k : ℕ) (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (cut : SinglePathSeed p ≃ X × Y)
    (theta : ℚ), theta < 1 →
    max 0 ((acceptanceRate p claim m - theta)/(1-theta)) ≤
      Heavy.heavyFraction Finset.univ (continuationRate p claim m cut) theta

theorem verification_suite : CryptoHiddenScalarSinglePathContractSuite where
  equivalence := fun _ _ _ _ _ _ _ _ _ => accepted_iff_verifies
  provenance := fun _ _ _ _ _ _ _ _ _ => produced_provenance
  heavy_prefix := by intros; apply heavy_prefix_lower; assumption

end CryptoHiddenScalarSinglePathContract
