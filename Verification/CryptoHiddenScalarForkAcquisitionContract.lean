/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarInnerProductCompressionContract
import Verification.CryptoBulletproofsIPATreeProbabilityContract

/-! Finite snapshot-indexed collection from one fixed adversary tape. Model
execution is not an implementation of an external process or a hardness claim. -/
namespace CryptoHiddenScalarForkAcquisitionContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
namespace C
export CryptoHiddenScalarInnerProductCompressionContract
  (ForkNode CompressedFork ValidCompressedFork responseClaim scalarCheck extractCompressed
   compressed_extraction_soundness)
end C
namespace F
export CryptoHiddenScalarInnerProductProtocolContract (Claim Announcement ResultValid)
end F
namespace P
export CryptoBulletproofsIPAPublicScalarBindingContract (toIPA ValidFork)
end P

inductive Rejection where
  | adversaryAbort | unexpectedMessage | duplicate | pedersen | leaf
  deriving DecidableEq, Repr
inductive Event where
  | query | restore | rejected (reason : Rejection) | exhausted
  deriving DecidableEq, Repr
abbrev ResourceTrace := List Event
namespace ResourceTrace
def oracleQueries (t : ResourceTrace) := t.count .query
def stateRestores (t : ResourceTrace) := t.count .restore
def candidateRejections (t : ResourceTrace) := (t.filter fun e => match e with
  | .rejected _ => true | _ => false).length
def subtreeFailures (t : ResourceTrace) := t.count .exhausted
end ResourceTrace
structure Attempt (α : Type) where
  value : Option α
  trace : ResourceTrace

def failed {α : Type} (r : Rejection) : Attempt α := ⟨none, [.rejected r]⟩

/-- Duplicates are compared only with successfully retained values. Each probe
logs restore first; a known duplicate skips the adversary call. -/
def scan {I V K : Type} [DecidableEq K] (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) : List I → List V → List V × ResourceTrace
  | [], acc => if acc.length = n then (acc, []) else (acc, [.exhausted])
  | i :: rest, acc =>
    if acc.length = n then (acc, []) else
    if label i ∈ acc.map key then
      let out := scan n label key attempt rest acc
      (out.1, .restore :: .rejected .duplicate :: out.2)
    else
      let a := attempt i
      let out := scan n label key attempt rest (match a.value with
        | none => acc | some v => acc ++ [v])
      (out.1, .restore :: (a.trace ++ out.2))

/-- Structural certification of the selected finite vector, not a validity
assumption about any adversary answer. -/
def select {V K : Type} [DecidableEq K] (n : ℕ) (key : V → K) (xs : List V) :
    Option {v : Fin n → V // Function.Injective (fun i => key (v i))} :=
  if h : xs.length = n then
    let v : Fin n → V := fun i => xs.get ⟨i.val, by omega⟩
    if hi : Function.Injective (fun i => key (v i)) then some ⟨v, hi⟩ else none
  else none

def collect {I V K : Type} [DecidableEq K] (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (is : List I) :
    Attempt {v : Fin n → V // Function.Injective (fun i => key (v i))} :=
  let out := scan n label key attempt is []
  ⟨select n key out.1, out.2⟩

theorem scan_trace_bound {I V K : Type} [DecidableEq K] (n : ℕ)
    (label : I → K) (key : V → K) (attempt : I → Attempt V) (bound : I → ℕ)
    (hb : ∀ i, (attempt i).trace.length ≤ bound i) (is : List I) (acc : List V) :
    (scan n label key attempt is acc).2.length ≤
      (is.map (fun i => 2 + bound i)).sum + 1 := by
  induction is generalizing acc with
  | nil => simp only [scan]; split_ifs <;> simp
  | cons i is ih =>
    simp only [scan]; split_ifs with h hdup
    · simp
    · have h := ih acc
      simp only [List.length_cons, List.map_cons, List.sum_cons] at *
      omega
    · have h := ih (match (attempt i).value with | none => acc | some v => acc ++ [v])
      have hi := hb i
      simp only [List.length_cons, List.length_append, List.map_cons, List.sum_cons] at *
      omega

/-- A rejection-free log contains only executed queries and restores. -/
def Clean (t : ResourceTrace) : Prop := ∀ e ∈ t, e = .query ∨ e = .restore

@[simp] theorem clean_nil : Clean [] := by simp [Clean]
@[simp] theorem clean_cons (e : Event) (t : ResourceTrace) :
    Clean (e :: t) ↔ (e = .query ∨ e = .restore) ∧ Clean t := by simp [Clean]
@[simp] theorem clean_append (a b : ResourceTrace) : Clean (a ++ b) ↔ Clean a ∧ Clean b := by
  simp [Clean, or_imp, forall_and]

/-- Exact cost of a clean scan, from costs of its actual child attempts. This
also proves quota completion and retained-key distinctness, not just a log bound. -/
theorem scan_clean_cost {I V K : Type} [DecidableEq K] (n : ℕ)
    (label : I → K) (key : V → K) (attempt : I → Attempt V) (q r : ℕ)
    (hc : ∀ i, Clean (attempt i).trace → ∃ v, (attempt i).value = some v ∧
      key v = label i ∧ (attempt i).trace.oracleQueries = q ∧
      (attempt i).trace.stateRestores = r)
    (is : List I) (acc : List V) (hl : acc.length ≤ n) (hd : (acc.map key).Nodup)
    (ht : Clean (scan n label key attempt is acc).2) :
    (scan n label key attempt is acc).1.length = n ∧
    ((scan n label key attempt is acc).1.map key).Nodup ∧
    (scan n label key attempt is acc).2.oracleQueries = (n - acc.length) * q ∧
    (scan n label key attempt is acc).2.stateRestores = (n - acc.length) * (r + 1) := by
  induction is generalizing acc with
  | nil =>
    by_cases h : acc.length = n
    · simp [scan, h, hd, ResourceTrace.oracleQueries, ResourceTrace.stateRestores]
    · simp [scan, h] at ht
  | cons i is ih =>
    by_cases h : acc.length = n
    · simp [scan, h, hd, ResourceTrace.oracleQueries, ResourceTrace.stateRestores]
    by_cases hi : label i ∈ acc.map key
    · simp [scan, h, hi] at ht
    have ht' : Clean (attempt i).trace ∧ Clean
        (scan n label key attempt is (match (attempt i).value with
          | none => acc | some v => acc ++ [v])).2 := by
      simpa [scan, h, hi] using ht
    obtain ⟨v, hv, hk, hq, hr⟩ := hc i ht'.1
    have hc' : Clean (scan n label key attempt is (acc ++ [v])).2 := by
      simpa [hv] using ht'.2
    have hd' : ((acc ++ [v]).map key).Nodup := by
      rw [List.map_append, List.map_singleton, hk, List.nodup_append_comm]
      exact List.nodup_cons.mpr ⟨hi, hd⟩
    have hl' : (acc ++ [v]).length ≤ n := by
      simp only [List.length_append, List.length_singleton]
      omega
    obtain ⟨htail, hdistinct, hqueries, hrestores⟩ := ih (acc ++ [v]) hl' hd' hc'
    have hsub : n - acc.length = 1 + (n - (acc ++ [v]).length) := by
      simp only [List.length_append, List.length_singleton]; omega
    simp only [scan, if_neg h, if_neg hi, hv]
    refine ⟨htail, hdistinct, ?_, ?_⟩
    · simp only [ResourceTrace.oracleQueries, List.count_cons, List.count_append,
        beq_iff_eq, reduceCtorEq, ↓reduceIte, Nat.add_zero] at *
      rw [hq, hqueries, hsub, Nat.add_mul, one_mul]
    · simp only [ResourceTrace.stateRestores, List.count_cons, List.count_append,
        beq_iff_eq, ↓reduceIte] at *
      rw [hr, hrestores, hsub, Nat.add_mul, one_mul]
      omega

inductive Request (q : ℕ) where
  | commit | outer (e : ZMod q) | binding (eta : (ZMod q)ˣ)
  | inner (depth : ℕ) (x : (ZMod q)ˣ)
  deriving DecidableEq
inductive Packet (q : ℕ) (A : Type) where
  | announcement (a : F.Announcement A)
  | scalar (t z : ZMod q)
  | round (m : RoundMessages A)
  | leaf (a b : ZMod q)

structure Snapshot (q : ℕ) (S : Type) where
  tapePos : ℕ
  history : List (Request q)
  memory : S

def advance {q : ℕ} {S : Type} (s : Snapshot q S) (req : Request q) (mem : S)
    (used : ℕ) : Snapshot q S := ⟨s.tapePos + used, s.history ++ [req], mem⟩

theorem step_tapePos_mono {q : ℕ} {S : Type} (s : Snapshot q S) (r : Request q)
    (mem : S) (n : ℕ) : s.tapePos ≤ (advance s r mem n).tapePos := by simp [advance]

structure AdversaryModel (q : ℕ) (A Ω S : Type) where
  tape : Ω
  initial : S
  step : Ω → Snapshot q S → Request q → Option (Packet q A × S × ℕ)

def initialSnapshot {q : ℕ} {A Ω S : Type} (m : AdversaryModel q A Ω S) : Snapshot q S :=
  ⟨0, [], m.initial⟩
inductive ReachableSnapshot {q : ℕ} {A Ω S : Type} (m : AdversaryModel q A Ω S) :
    Snapshot q S → Prop where
  | initial : ReachableSnapshot m (initialSnapshot m)
  | next {s req msg mem used} : ReachableSnapshot m s →
      m.step m.tape s req = some (msg, mem, used) →
      ReachableSnapshot m (advance s req mem used)

abbrev restore {q : ℕ} {A Ω S : Type} (m : AdversaryModel q A Ω S)
    (s : {s // ReachableSnapshot m s}) : Snapshot q S := s.val

theorem restore_eq_snapshot {q : ℕ} {A Ω S : Type} (m : AdversaryModel q A Ω S)
    (s : {s // ReachableSnapshot m s}) : restore m s = s.val := rfl

theorem step_deterministic {q : ℕ} {A Ω S : Type} (m : AdversaryModel q A Ω S)
    (s t : Snapshot q S) (h : s = t) (r : Request q) :
    m.step m.tape s r = m.step m.tape t r := by rw [h]

/-- A successful primitive observation carries the actual transition equation. -/
structure Observation {q : ℕ} {A Ω S : Type} (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (r : Request q) where
  packet : Packet q A
  memory : S
  used : ℕ
  equation : m.step m.tape s r = some (packet, memory, used)

def query {q : ℕ} {A Ω S : Type} (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (r : Request q) : Option (Observation m s r) :=
  match h : m.step m.tape s r with
  | none => none
  | some (p, mem, n) => some ⟨p, mem, n, h⟩

def Observation.after {q : ℕ} {A Ω S : Type} {m : AdversaryModel q A Ω S}
    {s : Snapshot q S} {r : Request q} (o : Observation m s r) := advance s r o.memory o.used

theorem Observation.reachable {q : ℕ} {A Ω S : Type} {m : AdversaryModel q A Ω S}
    {s : Snapshot q S} {r : Request q} (o : Observation m s r)
    (hs : ReachableSnapshot m s) : ReachableSnapshot m o.after :=
  .next hs o.equation

/-- Every retry occurrence owns its own child schedule, even for equal calls. -/
abbrev IPASchedule (q : ℕ) : ℕ → Type
  | 0 => Unit
  | d + 1 => List ((ZMod q)ˣ × IPASchedule q d)
abbrev EtaSchedule (q k : ℕ) := List ((ZMod q)ˣ × IPASchedule q k)
abbrev ProbeSchedule (q k : ℕ) := List (ZMod q × EtaSchedule q k)

variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
  [DecidableEq A] {Ω S : Type} {k : ℕ}

/-- Provenance is a relation on transition equations, independent of validity. -/
def TreeOrigin (m : AdversaryModel q A Ω S) : {d : ℕ} → Snapshot q S → Packet q A →
    IPATranscriptTree q A d → Prop
  | 0, _, msg, .leaf _ a b => msg = .leaf a b
  | d + 1, s, msg, .node _ lr xs ts => msg = .round lr ∧
      ∀ i, ∃ (x : (ZMod q)ˣ) (o : Observation m s (.inner d x)),
        (x : ZMod q) = xs i ∧ TreeOrigin m o.after o.packet (ts i)

abbrev AcquiredTree (m : AdversaryModel q A Ω S) (s : Snapshot q S) (msg : Packet q A)
    (st : Statement q A k) :=
  {t : IPATranscriptTree q A k // ValidAcceptingTree st t ∧ TreeOrigin m s msg t}

/-- Recursive collector transports the concrete child snapshot, never just st. -/
def acquireTree (m : AdversaryModel q A Ω S) : {d : ℕ} →
    (s : Snapshot q S) → ReachableSnapshot m s → (msg : Packet q A) →
    (st : Statement q A d) → IPASchedule q d → Attempt (AcquiredTree m s msg st)
  | 0, s, _, msg, st, _ => match hm : msg with
    | .leaf a b =>
      if hv : ValidAcceptingTree st (.leaf st a b) then
        ⟨some ⟨.leaf st a b, hv, rfl⟩, []⟩ else failed .leaf
    | _ => failed .unexpectedMessage
  | d + 1, s, hs, msg, st, schedule => match hm : msg with
    | .round lr =>
      let candidate := fun (p : (ZMod q)ˣ × IPASchedule q d) =>
        match query m (restore m ⟨s, hs⟩) (.inner d p.1) with
        | none => ⟨none, [.query, .rejected .adversaryAbort]⟩
        | some o =>
          let a := acquireTree m o.after (o.reachable hs) o.packet
            (child_statement st lr p.1) p.2
          ⟨a.value.map (fun t => (⟨p.1, o, t⟩ :
            Σ x : (ZMod q)ˣ, Σ ob : Observation m s (.inner d x),
              AcquiredTree m ob.after ob.packet (child_statement st lr x))), .query :: a.trace⟩
      let out := collect 4 (fun p => (p.1 : ZMod q)^2)
        (fun v => (v.1 : ZMod q)^2) candidate schedule
      match out.value with
      | none => ⟨none, out.trace⟩
      | some v =>
        let xs : Fin 4 → (ZMod q)ˣ := fun i => (v.val i).1
        let trees := fun i => (v.val i).2.2.val
        let tree := IPATranscriptTree.node st lr (fun i => (xs i : ZMod q)) trees
        have hv : ValidAcceptingTree st tree := by
          refine ⟨rfl, ?_⟩
          simp only [xs, dif_pos (fun i => Units.ne_zero ((v.val i).1))]
          refine ⟨v.property, fun i => ?_⟩
          simpa using (v.val i).2.2.property.1
        have hp : TreeOrigin m s (.round lr) tree :=
          ⟨rfl, fun i => ⟨xs i, (v.val i).2.1, rfl, (v.val i).2.2.property.2⟩⟩
        ⟨some ⟨tree, hv, hp⟩, out.trace⟩
    | _ => failed .unexpectedMessage


/-- Actual e and eta observations with their exact resulting snapshots. -/
def NodeOrigin (m : AdversaryModel q A Ω S) (s : Snapshot q S) (n : C.ForkNode q A k) : Prop :=
  ∃ o : Observation m s (.outer n.challenge), o.packet = .scalar n.product n.blind ∧
    (∃ a : Observation m o.after (.binding n.eta₀), TreeOrigin m a.after a.packet n.tree₀) ∧
    (∃ b : Observation m o.after (.binding n.eta₁), TreeOrigin m b.after b.packet n.tree₁)

abbrev NodeValid (p : F.Claim q A k) (ann : F.Announcement A) (n : C.ForkNode q A k) : Prop :=
  C.scalarCheck p ann n.challenge n.product n.blind ∧
    P.ValidFork (C.responseClaim p ann n.challenge n.product)
      n.eta₀ n.eta₁ n.tree₀ n.tree₁

abbrev AcquiredNode (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (ann : F.Announcement A) :=
  {n : C.ForkNode q A k // NodeValid p ann n ∧ NodeOrigin m s n}

def acquireNode (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A)
    (e : ZMod q) (schedule : EtaSchedule q k) : Attempt (AcquiredNode p m s ann) :=
  match query m (restore m ⟨s, hs⟩) (.outer e) with
  | none => ⟨none, [.query, .rejected .adversaryAbort]⟩
  | some o => match he : o.packet with
    | .scalar t z =>
      if hv : C.scalarCheck p ann e t z then
        let candidate := fun (pr : (ZMod q)ˣ × IPASchedule q k) =>
          match query m (restore m ⟨o.after, o.reachable hs⟩) (.binding pr.1) with
          | none => ⟨none, [.query, .rejected .adversaryAbort]⟩
          | some b =>
            let a := acquireTree m b.after (b.reachable (o.reachable hs)) b.packet
              (P.toIPA (C.responseClaim p ann e t) pr.1) pr.2
            ⟨a.value.map (fun tr => (⟨pr.1, b, tr⟩ :
              Σ eta : (ZMod q)ˣ, Σ ob : Observation m o.after (.binding eta),
                AcquiredTree m ob.after ob.packet (P.toIPA (C.responseClaim p ann e t) eta))),
              .query :: a.trace⟩
        let out := collect 2 Prod.fst (fun v => v.1) candidate schedule
        match out.value with
        | none => ⟨none, .query :: out.trace⟩
        | some v =>
          ⟨some ⟨⟨e, t, z, (v.val 0).1, (v.val 1).1,
            (v.val 0).2.2.val, (v.val 1).2.2.val⟩,
            ⟨hv, v.property.ne (by decide : (0 : Fin 2) ≠ 1),
              (v.val 0).2.2.property.1, (v.val 1).2.2.property.1⟩,
            ⟨o, he, ⟨(v.val 0).2.1, (v.val 0).2.2.property.2⟩,
              ⟨(v.val 1).2.1, (v.val 1).2.2.property.2⟩⟩⟩, .query :: out.trace⟩
      else ⟨none, [.query, .rejected .pedersen]⟩
    | _ => ⟨none, [.query, .rejected .unexpectedMessage]⟩

def ForkProvenance (m : AdversaryModel q A Ω S) (f : C.CompressedFork q A k) : Prop :=
  ∃ o : Observation m (initialSnapshot m) .commit,
    o.packet = .announcement f.announcement ∧ ∀ i, NodeOrigin m o.after (f.nodes i)

inductive AcquireError where
  | initialAdversaryAbort | exhaustedE
  deriving DecidableEq, Repr
structure AcquisitionRun (q : ℕ) (A : Type) (k : ℕ) where
  outcome : Except AcquireError (C.CompressedFork q A k)
  trace : ResourceTrace

abbrev CertifiedFork (p : F.Claim q A k) (m : AdversaryModel q A Ω S) :=
  {f : C.CompressedFork q A k // C.ValidCompressedFork p f ∧ ForkProvenance m f}

/-- Internal proof fields are erased by code generation. No accepting trees or
validity assumptions are inputs to this algorithm. -/
def acquireCertified (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (schedule : ProbeSchedule q k) : Except AcquireError (CertifiedFork p m) × ResourceTrace :=
  match query m (initialSnapshot m) .commit with
  | none => (.error .initialAdversaryAbort, [.query, .rejected .adversaryAbort])
  | some o => match hc : o.packet with
    | .announcement ann =>
      let out := collect 3 Prod.fst (fun v => v.val.challenge)
        (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2) schedule
      match out.value with
      | none => (.error .exhaustedE, .query :: out.trace)
      | some v =>
        (.ok ⟨⟨ann, fun i => (v.val i).val⟩,
          ⟨v.property, fun i => (v.val i).property.1⟩,
          ⟨o, hc, fun i => (v.val i).property.2⟩⟩, .query :: out.trace)
    | _ => (.error .initialAdversaryAbort, [.query, .rejected .unexpectedMessage])

def acquireCompressedFork (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (schedule : ProbeSchedule q k) : AcquisitionRun q A k :=
  let a := acquireCertified p m schedule
  ⟨a.1.map Subtype.val, a.2⟩

theorem acquire_provenance_and_valid (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (schedule : ProbeSchedule q k) (f : C.CompressedFork q A k)
    (h : (acquireCompressedFork p m schedule).outcome = .ok f) :
    C.ValidCompressedFork p f ∧ ForkProvenance m f := by
  unfold acquireCompressedFork at h
  cases he : (acquireCertified p m schedule).1 with
  | error e => simp only [he, Except.map] at h; cases h
  | ok v =>
    simp only [he, Except.map, Except.ok.injEq] at h
    subst f
    exact v.property

theorem acquire_provenance_sound (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (schedule : ProbeSchedule q k) (f : C.CompressedFork q A k)
    (h : (acquireCompressedFork p m schedule).outcome = .ok f) : ForkProvenance m f :=
  (acquire_provenance_and_valid p m schedule f h).2

theorem acquire_valid_compressed_fork (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (schedule : ProbeSchedule q k) (f : C.CompressedFork q A k)
    (h : (acquireCompressedFork p m schedule).outcome = .ok f) : C.ValidCompressedFork p f :=
  (acquire_provenance_and_valid p m schedule f h).1

theorem acquire_and_extract_soundness (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (schedule : ProbeSchedule q k) (f : C.CompressedFork q A k)
    (h : (acquireCompressedFork p m schedule).outcome = .ok f) :
    F.ResultValid p (C.extractCompressed p f) :=
  C.compressed_extraction_soundness p f (acquire_valid_compressed_fork p m schedule f h)


/-- Schedule-only upper bound, including exhaustion and rejection events. -/
def treeFuel (q : ℕ) : {d : ℕ} → IPASchedule q d → ℕ
  | 0, _ => 1
  | _ + 1, ps => (ps.map (fun p => 4 + treeFuel q p.2)).sum + 1

def nodeFuel (ps : EtaSchedule q k) : ℕ :=
  (ps.map (fun p => 4 + treeFuel q p.2)).sum + 3

def scheduleFuel (ps : ProbeSchedule q k) : ℕ :=
  (ps.map (fun p => 2 + nodeFuel p.2)).sum + 3

theorem collect_trace_bound {I V K : Type} [DecidableEq K] (n : ℕ)
    (label : I → K) (key : V → K) (attempt : I → Attempt V) (bound : I → ℕ)
    (hb : ∀ i, (attempt i).trace.length ≤ bound i) (is : List I) :
    (collect n label key attempt is).trace.length ≤
      (is.map (fun i => 2 + bound i)).sum + 1 :=
  scan_trace_bound n label key attempt bound hb is []

theorem tree_trace_bound (m : AdversaryModel q A Ω S) : ∀ {d : ℕ}
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (msg : Packet q A)
    (st : Statement q A d) (ps : IPASchedule q d),
    (acquireTree m s hs msg st ps).trace.length ≤ treeFuel q ps := by
  intro d
  induction d with
  | zero =>
    intro s hs msg st ps
    cases msg <;> simp only [acquireTree, failed, treeFuel, List.length_singleton]
    all_goals first | exact le_rfl | (split <;> simp)
  | succ d ih =>
    intro s hs msg st ps
    cases msg with
    | round lr =>
      unfold acquireTree
      dsimp -zeta only
      extract_lets candidate out
      have hb := collect_trace_bound 4
        (fun p : (ZMod q)ˣ × IPASchedule q d => (p.1 : ZMod q)^2)
        (fun v => (v.1 : ZMod q)^2) candidate (fun p => 2 + treeFuel q p.2)
        (by
          intro pr
          dsimp only [candidate]
          split
          · simp
          · rename_i ob he
            have h := ih ob.after (ob.reachable hs) ob.packet
              (child_statement st lr pr.1) pr.2
            simp only [List.length_cons]
            omega) ps
      split <;> simpa only [out, treeFuel, ← Nat.add_assoc, show 2 + 2 = 4 from rfl] using hb
    | announcement a => simp [acquireTree, failed, treeFuel]
    | scalar t z => simp [acquireTree, failed, treeFuel]
    | leaf a b => simp [acquireTree, failed, treeFuel]


theorem node_trace_bound (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A)
    (e : ZMod q) (ps : EtaSchedule q k) :
    (acquireNode p m s hs ann e ps).trace.length ≤ nodeFuel ps := by
  unfold acquireNode
  split
  · simp [nodeFuel]
  · rename_i o ho
    split
    · rename_i t z he
      split
      · extract_lets candidate out
        have hb := collect_trace_bound 2 Prod.fst (fun v => v.1) candidate
          (fun pr => 2 + treeFuel q pr.2) (by
            intro pr
            dsimp only [candidate]
            split
            · simp
            · rename_i b hb
              have h := tree_trace_bound m b.after (b.reachable (o.reachable hs)) b.packet
                (P.toIPA (C.responseClaim p ann e t) pr.1) pr.2
              simp only [List.length_cons]
              omega) ps
        have h : out.trace.length ≤ (ps.map (fun pr => 4 + treeFuel q pr.2)).sum + 1 := by
          simpa only [out, ← Nat.add_assoc, show 2+2=4 from rfl] using hb
        split <;> simp only [List.length_cons, nodeFuel] <;> omega
      · simp [nodeFuel]
    · simp [nodeFuel]

theorem acquisition_trace_bound (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (ps : ProbeSchedule q k) :
    (acquireCompressedFork p m ps).trace.length ≤ scheduleFuel ps := by
  unfold acquireCompressedFork acquireCertified
  split
  · simp [scheduleFuel]
  · rename_i o ho
    split
    · rename_i ann hc
      extract_lets out a
      have hb := collect_trace_bound 3 Prod.fst (fun v => v.val.challenge)
        (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2)
        (fun pr => nodeFuel pr.2)
        (fun pr => node_trace_bound p m o.after (o.reachable .initial) ann pr.1 pr.2) ps
      have h : out.trace.length ≤ (ps.map (fun pr => 2 + nodeFuel pr.2)).sum + 1 := hb
      dsimp only [a]
      split <;> simp only [List.length_cons, scheduleFuel] <;> omega
    · simp [scheduleFuel]

/-- Every counter is bounded on failures too; no log is discarded. -/
theorem resource_bounds (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (ps : ProbeSchedule q k) :
    let t := (acquireCompressedFork p m ps).trace
    t.oracleQueries ≤ scheduleFuel ps ∧ t.stateRestores ≤ scheduleFuel ps ∧
    t.candidateRejections ≤ scheduleFuel ps ∧ t.subtreeFailures ≤ scheduleFuel ps := by
  have h := acquisition_trace_bound p m ps
  exact ⟨List.count_le_length.trans h, List.count_le_length.trans h,
    (List.length_filter_le _ _).trans h, List.count_le_length.trans h⟩


/-- Successful-prefix operational certificate. It mentions actual local attempt
results and retained keys, not algebraic validity of a completed fork. -/
inductive ScanSuccess {I V K : Type} [DecidableEq K] (n : ℕ)
    (label : I → K) (key : V → K) (attempt : I → Attempt V) :
    List I → List V → Prop where
  | done {is acc} : acc.length = n → (acc.map key).Nodup → ScanSuccess n label key attempt is acc
  | skip {i is acc} : acc.length ≠ n → label i ∈ acc.map key →
      ScanSuccess n label key attempt is acc → ScanSuccess n label key attempt (i :: is) acc
  | failure {i is acc} : acc.length ≠ n → label i ∉ acc.map key →
      (attempt i).value = none → ScanSuccess n label key attempt is acc →
      ScanSuccess n label key attempt (i :: is) acc
  | success {i is acc v} : acc.length ≠ n → label i ∉ acc.map key →
      (attempt i).value = some v → ScanSuccess n label key attempt is (acc ++ [v]) →
      ScanSuccess n label key attempt (i :: is) acc

theorem scan_success {I V K : Type} [DecidableEq K] (n : ℕ)
    (label : I → K) (key : V → K) (attempt : I → Attempt V) (is : List I) (acc : List V)
    (h : ScanSuccess n label key attempt is acc) :
    (scan n label key attempt is acc).1.length = n ∧
    ((scan n label key attempt is acc).1.map key).Nodup := by
  induction h with
  | @done is acc hl hd => cases is <;> simpa [scan, hl] using And.intro hl hd
  | skip hl hd _ ih => simpa [scan, hl, hd] using ih
  | failure hl hd hf _ ih => simpa [scan, hl, hd, hf] using ih
  | success hl hd hf _ ih => simpa [scan, hl, hd, hf] using ih

theorem select_success {V K : Type} [DecidableEq K] (n : ℕ) (key : V → K) (xs : List V)
    (hl : xs.length = n) (hd : (xs.map key).Nodup) : (select n key xs).isSome = true := by
  have hi : Function.Injective (fun i : Fin n => key (xs.get ⟨i.val, by omega⟩)) := by
    intro i j hij
    have h := List.nodup_iff_injective_get.mp hd
    have he : (⟨i.val, by simp [hl]⟩ : Fin (xs.map key).length) =
        ⟨j.val, by simp [hl]⟩ := h (by simpa using hij)
    exact Fin.ext (congrArg (fun x : Fin (xs.map key).length => x.val) he)
  simp only [select, dif_pos hl, dif_pos hi, Option.isSome_some]

theorem collect_success {I V K : Type} [DecidableEq K] (n : ℕ)
    (label : I → K) (key : V → K) (attempt : I → Attempt V) (is : List I)
    (h : ScanSuccess n label key attempt is []) :
    (collect n label key attempt is).value.isSome = true :=
  select_success n key _ (scan_success n label key attempt is [] h).1
    (scan_success n label key attempt is [] h).2


theorem collect_clean_cost {I V K : Type} [DecidableEq K] (n : ℕ)
    (label : I → K) (key : V → K) (attempt : I → Attempt V) (q r : ℕ)
    (hc : ∀ i, Clean (attempt i).trace → ∃ v, (attempt i).value = some v ∧
      key v = label i ∧ (attempt i).trace.oracleQueries = q ∧
      (attempt i).trace.stateRestores = r)
    (is : List I) (ht : Clean (collect n label key attempt is).trace) :
    (collect n label key attempt is).value.isSome = true ∧
    (collect n label key attempt is).trace.oracleQueries = n * q ∧
    (collect n label key attempt is).trace.stateRestores = n * (r + 1) := by
  obtain ⟨hl, hd, hq, hr⟩ := scan_clean_cost n label key attempt q r hc is []
    (Nat.zero_le _) (by simp) ht
  exact ⟨select_success n key _ hl hd, hq, hr⟩

/-- Local search evidence at the reachable post-commit snapshot. Children are
actual snapshot-indexed attempts, including their own finite retry schedules. -/
def AcquisitionSupport (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (ps : ProbeSchedule q k) : Prop :=
  ∃ (o : Observation m (initialSnapshot m) .commit) (ann : F.Announcement A),
    query m (initialSnapshot m) .commit = some o ∧ o.packet = .announcement ann ∧
    ScanSuccess 3 Prod.fst (fun v => v.val.challenge)
      (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2) ps []

theorem support_acquires (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (ps : ProbeSchedule q k) (h : AcquisitionSupport p m ps) :
    ∃ f, (acquireCompressedFork p m ps).outcome = .ok f := by
  obtain ⟨o, ann, ho, ha, hs⟩ := h
  have hc := collect_success 3 Prod.fst (fun v => v.val.challenge)
    (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2) ps hs
  unfold acquireCompressedFork acquireCertified
  simp only [ho]
  split
  · rename_i ann' ha'
    have he : ann' = ann := Packet.announcement.inj (ha'.symm.trans ha)
    subst ann'
    split
    · rename_i hz
      simp [hz] at hc
    · exact ⟨_, rfl⟩
  · rename_i hbad
    exact False.elim (hbad ann ha)

namespace Prob
export CryptoBulletproofsIPATreeProbabilityContract
  (probability passing ConditionalBounds sequential_probability_lower probability_mono
   positive_probability_has_outcome)
end Prob

/-- Uniform finite seeds may encode independent product schedules or correlated
schedules. Bounds must be established on these SAME seeds, conditioned on prior
local tests. The realizes premise is operational search evidence, not an
assumed ValidCompressedFork. No context-only source is substituted for snapshots. -/
theorem acquisition_probability_lower {Seed : Type} [DecidableEq Seed]
    (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (D : Finset Seed) (hD : D.Nonempty) (schedule : Seed → ProbeSchedule q k)
    (tests : List (Seed → Bool)) (bounds : List ℚ)
    (hd : Prob.ConditionalBounds D tests bounds)
    (realizes : ∀ w ∈ Prob.passing D tests, AcquisitionSupport p m (schedule w)) :
    bounds.prod ≤ Prob.probability D
      (D.filter fun w => (acquireCompressedFork p m (schedule w)).outcome.isOk) := by
  apply (Prob.sequential_probability_lower D hD tests bounds hd).trans
  apply Prob.probability_mono
  intro w hw
  obtain ⟨f, hf⟩ := support_acquires p m (schedule w) (realizes w hw)
  exact Finset.mem_filter.mpr
    ⟨(CryptoBulletproofsIPATreeProbabilityContract.passing_subset D tests) hw,
    by simp [hf, Except.isOk, Except.toBool]⟩

theorem positive_schedule_probability_extracts {Seed : Type} [DecidableEq Seed]
    (p : F.Claim q A k) (m : AdversaryModel q A Ω S) (D : Finset Seed)
    (schedule : Seed → ProbeSchedule q k)
    (hp : 0 < Prob.probability D
      (D.filter fun w => (acquireCompressedFork p m (schedule w)).outcome.isOk)) :
    ∃ w ∈ D, ∃ f, (acquireCompressedFork p m (schedule w)).outcome = .ok f ∧
      ForkProvenance m f ∧ F.ResultValid p (C.extractCompressed p f) := by
  obtain ⟨w, hw, hs⟩ := Prob.positive_probability_has_outcome _ _ hp
  have ho := (Finset.mem_filter.mp hs).2
  cases he : (acquireCompressedFork p m (schedule w)).outcome with
  | error err => simp [he, Except.isOk, Except.toBool] at ho
  | ok f => exact ⟨w, hw, f, he, acquire_provenance_sound p m _ f he,
      acquire_and_extract_soundness p m _ f he⟩

/-- Additional finite density estimates are hypotheses, not consequences of a
single marginal acceptance rate. In particular an empty outer schedule fails. -/
theorem empty_schedule_no_fork (p : F.Claim q A k) (m : AdversaryModel q A Ω S) :
    (acquireCompressedFork p m []).outcome.isOk = false := by
  unfold acquireCompressedFork acquireCertified
  split
  · rfl
  · split
    · simp [collect, scan, select, Except.map, Except.isOk, Except.toBool]
    · rfl

/-- Exact primitive workload of the complete, rejection-free traversal skeleton.
Each IPA root is produced by eta, so it must not be counted twice. -/
def idealTreeQueries : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + 4 * idealTreeQueries d

def idealQueries (d : ℕ) := 1 + 3 * (1 + 2 * idealTreeQueries d)
def idealRestores (d : ℕ) := idealQueries d - 1

theorem ideal_tree_geometric (d : ℕ) : 3 * idealTreeQueries d = 4^(d+1)-1 := by
  have hp : ∀ n : ℕ, 0 < 4^n := fun n => pow_pos (by decide) n
  induction d with
  | zero => rfl
  | succ d ih => rw [idealTreeQueries, pow_succ]; have := hp (d+1); omega

theorem ideal_queries_closed (d : ℕ) : idealQueries d = 4 + 2*(4^(d+1)-1) := by
  have h := ideal_tree_geometric d
  unfold idealQueries
  omega

theorem ideal_restores_closed (d : ℕ) : idealRestores d = idealQueries d - 1 := rfl

theorem ideal_tree_positive (d : ℕ) : 0 < idealTreeQueries d := by
  cases d <;> simp [idealTreeQueries]

set_option backward.isDefEq.respectTransparency false in
theorem tree_clean_cost (m : AdversaryModel q A Ω S) : ∀ {d : ℕ}
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (msg : Packet q A)
    (st : Statement q A d) (ps : IPASchedule q d),
    Clean (acquireTree m s hs msg st ps).trace →
    (acquireTree m s hs msg st ps).value.isSome = true ∧
    (acquireTree m s hs msg st ps).trace.oracleQueries = idealTreeQueries d - 1 ∧
    (acquireTree m s hs msg st ps).trace.stateRestores = idealTreeQueries d - 1 := by
  intro d
  induction d with
  | zero =>
    intro s hs msg st ps ht
    cases msg <;> simp only [acquireTree] at *
    all_goals try { simp [failed] at ht }
    split <;> simp_all [failed, idealTreeQueries, ResourceTrace.oracleQueries,
      ResourceTrace.stateRestores]
  | succ d ih =>
    intro s hs msg st ps ht
    cases msg with
    | round lr =>
      unfold acquireTree at ht ⊢
      dsimp -zeta only at ht ⊢
      extract_lets candidate out at ht
      have ht' : Clean out.trace := by split at ht <;> exact ht
      have hc := collect_clean_cost 4
        (fun p : (ZMod q)ˣ × IPASchedule q d => (p.1 : ZMod q)^2)
        (fun v => (v.1 : ZMod q)^2) candidate (idealTreeQueries d) (idealTreeQueries d - 1)
        (by
          intro pr hp
          dsimp only [candidate] at hp ⊢
          split
          · rename_i he
            simp [he] at hp
          · rename_i ob he
            have hclean : Clean (acquireTree m ob.after (ob.reachable hs) ob.packet
                (child_statement st lr pr.1) pr.2).trace := by simpa [he] using hp
            obtain ⟨hv, hq, hr⟩ := ih ob.after (ob.reachable hs) ob.packet
              (child_statement st lr pr.1) pr.2 hclean
            cases he : (acquireTree m ob.after (ob.reachable hs) ob.packet
                (child_statement st lr pr.1) pr.2).value with
            | none => simp [he] at hv
            | some v =>
              refine ⟨⟨pr.1,ob,v⟩, rfl, rfl, ?_, ?_⟩
              · simp only [ResourceTrace.oracleQueries, List.count_cons,
                  beq_iff_eq, ↓reduceIte] at *
                have := ideal_tree_positive d
                omega
              · simpa only [ResourceTrace.stateRestores, List.count_cons,
                  beq_iff_eq, reduceCtorEq, ↓reduceIte, Nat.add_zero] using hr) ps ht'
      have hp := ideal_tree_positive d
      have hsub : idealTreeQueries d - 1 + 1 = idealTreeQueries d := by omega
      dsimp only
      split
      · rename_i hn
        have hv := hc.1
        change out.value.isSome = true at hv
        have hn' : out.value = none := hn
        rw [hn'] at hv
        cases hv
      · exact ⟨rfl, by simpa [idealTreeQueries] using hc.2.1,
          by simpa [idealTreeQueries, hsub] using hc.2.2⟩
    | announcement a => simp [acquireTree, failed] at ht
    | scalar t z => simp [acquireTree, failed] at ht
    | leaf a b => simp [acquireTree, failed] at ht

set_option backward.isDefEq.respectTransparency false in
theorem node_clean_cost (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A)
    (e : ZMod q) (ps : EtaSchedule q k) (ht : Clean (acquireNode p m s hs ann e ps).trace) :
    ∃ v, (acquireNode p m s hs ann e ps).value = some v ∧ v.val.challenge = e ∧
      (acquireNode p m s hs ann e ps).trace.oracleQueries = 1 + 2 * idealTreeQueries k ∧
      (acquireNode p m s hs ann e ps).trace.stateRestores = 2 * idealTreeQueries k := by
  unfold acquireNode at ht ⊢
  split
  · rename_i he
    simp [he] at ht
  · rename_i o ho
    simp only [ho] at ht
    split
    · rename_i t z he
      split at ht
      · rename_i t' z' he'
        have hh := Packet.scalar.inj (he'.symm.trans he)
        obtain ⟨hleft, hright⟩ := hh
        subst t'
        subst z'
        split
        · rename_i hv
          simp only [dif_pos hv] at ht
          try intro ht
          extract_lets candidate out
          have ht' : Clean out.trace := by split at ht <;> simpa using ht
          have hc := collect_clean_cost 2 Prod.fst (fun v => v.1) candidate
            (idealTreeQueries k) (idealTreeQueries k - 1) (by
              intro pr hp
              dsimp only [candidate] at hp ⊢
              split
              · rename_i he
                simp [he] at hp
              · rename_i ob he
                have hclean : Clean (acquireTree m ob.after (ob.reachable (o.reachable hs))
                    ob.packet (P.toIPA (C.responseClaim p ann e t) pr.1) pr.2).trace := by
                  simpa [he] using hp
                obtain ⟨hval, hq, hr⟩ := tree_clean_cost m ob.after
                  (ob.reachable (o.reachable hs)) ob.packet
                  (P.toIPA (C.responseClaim p ann e t) pr.1) pr.2 hclean
                cases he : (acquireTree m ob.after (ob.reachable (o.reachable hs)) ob.packet
                    (P.toIPA (C.responseClaim p ann e t) pr.1) pr.2).value with
                | none => simp [he] at hval
                | some v =>
                  refine ⟨⟨pr.1,ob,v⟩, rfl, rfl, ?_, ?_⟩
                  · simp only [ResourceTrace.oracleQueries, List.count_cons,
                      beq_iff_eq, ↓reduceIte] at *
                    have := ideal_tree_positive k
                    omega
                  · simpa only [ResourceTrace.stateRestores, List.count_cons,
                      beq_iff_eq, reduceCtorEq, ↓reduceIte, Nat.add_zero] using hr) ps ht'
          split
          · rename_i hn
            have hval := hc.1
            have hn' : out.value = none := hn
            change out.value.isSome = true at hval
            rw [hn'] at hval
            cases hval
          · refine ⟨_, rfl, rfl, ?_, ?_⟩
            · have hq := hc.2.1
              change out.trace.oracleQueries = 2 * idealTreeQueries k at hq
              simp only [ResourceTrace.oracleQueries, List.count_cons,
                beq_iff_eq, ↓reduceIte] at *
              omega
            · have hr := hc.2.2
              change out.trace.stateRestores = 2 * (idealTreeQueries k - 1 + 1) at hr
              have hp := ideal_tree_positive k
              have hh : idealTreeQueries k - 1 + 1 = idealTreeQueries k := by omega
              simpa only [ResourceTrace.stateRestores, List.count_cons,
                beq_iff_eq, reduceCtorEq, ↓reduceIte, Nat.add_zero, hh] using hr
        · rename_i hv
          simp [dif_neg hv] at ht
      · rename_i hbad
        exact False.elim (hbad t z he)
    · rename_i he
      split at ht
      · rename_i aa bb hh
        exact False.elim (he aa bb hh)
      · simp at ht

set_option backward.isDefEq.respectTransparency false in
theorem clean_acquisition_exact (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (ps : ProbeSchedule q k) (ht : Clean (acquireCompressedFork p m ps).trace) :
    (acquireCompressedFork p m ps).outcome.isOk = true ∧
    (acquireCompressedFork p m ps).trace.oracleQueries = idealQueries k ∧
    (acquireCompressedFork p m ps).trace.stateRestores = idealQueries k - 1 := by
  unfold acquireCompressedFork acquireCertified at ht ⊢
  split
  · rename_i he
    simp [he] at ht
  · rename_i o ho
    simp only [ho] at ht
    split
    · rename_i ann ha
      split at ht
      · rename_i ann' ha'
        have hh : ann' = ann := Packet.announcement.inj (ha'.symm.trans ha)
        subst ann'
        try intro ht
        extract_lets out a
        have ht' : Clean out.trace := by split at ht <;> simpa using ht
        have hc := collect_clean_cost 3 Prod.fst (fun v => v.val.challenge)
          (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2)
          (1 + 2 * idealTreeQueries k) (2 * idealTreeQueries k)
          (fun pr h => node_clean_cost p m o.after (o.reachable .initial) ann pr.1 pr.2 h) ps ht'
        dsimp only [a]
        split
        · rename_i hn
          have hval := hc.1
          have hn' : out.value = none := hn
          change out.value.isSome = true at hval
          rw [hn'] at hval
          cases hval
        · refine ⟨rfl, ?_, ?_⟩
          · have hq := hc.2.1
            change out.trace.oracleQueries = 3 * (1 + 2 * idealTreeQueries k) at hq
            simp only [ResourceTrace.oracleQueries, List.count_cons, beq_iff_eq,
              ↓reduceIte, idealQueries] at *
            omega
          · have hr := hc.2.2
            change out.trace.stateRestores = 3 * (2 * idealTreeQueries k + 1) at hr
            simp only [ResourceTrace.stateRestores, List.count_cons, beq_iff_eq,
              reduceCtorEq, ↓reduceIte, Nat.add_zero, idealQueries] at *
            omega
      · rename_i hbad
        exact False.elim (hbad ann ha)
    · rename_i he
      split at ht
      · rename_i aa hh
        exact False.elim (he aa hh)
      · simp at ht

/-- Fixed-length tests of the actual executed log. Missing positions pass;
rejections/exhaustions fail. The finite fuel bound makes padding exact. -/
def traceTests {Seed : Type} (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (schedule : Seed → ProbeSchedule q k) (N : ℕ) : List (Seed → Bool) :=
  List.ofFn fun i : Fin N => fun w =>
    match (acquireCompressedFork p m (schedule w)).trace[i.val]? with
    | none => true
    | some .query | some .restore => true
    | _ => false

theorem trace_tests_clean {Seed : Type} (p : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (schedule : Seed → ProbeSchedule q k) (N : ℕ)
    (w : Seed) (hn : scheduleFuel (schedule w) ≤ N)
    (ht : (traceTests p m schedule N).all (fun f => f w) = true) :
    Clean (acquireCompressedFork p m (schedule w)).trace := by
  intro e he
  obtain ⟨i, hi, hv⟩ := List.mem_iff_getElem.mp he
  have hiN : i < N := lt_of_lt_of_le hi ((acquisition_trace_bound p m (schedule w)).trans hn)
  have hh := (List.all_eq_true.mp ht) _ (List.mem_ofFn.mpr ⟨⟨i,hiN⟩, rfl⟩)
  simp only [List.getElem?_eq_getElem hi, hv] at hh
  cases e <;> simp_all

/-- Concrete execution-to-probability bridge. Conditional bounds are on each
actual log position after all earlier tests, so snapshots/history are retained.
This conservative bound counts clean schedules; successful retries may add mass.
It does not assert the density assumptions for an arbitrary adversary. -/
theorem clean_schedule_probability_lower {Seed : Type} [DecidableEq Seed]
    (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (D : Finset Seed) (hD : D.Nonempty) (schedule : Seed → ProbeSchedule q k)
    (N : ℕ) (hn : ∀ w ∈ D, scheduleFuel (schedule w) ≤ N) (bounds : List ℚ)
    (hd : Prob.ConditionalBounds D (traceTests p m schedule N) bounds) :
    bounds.prod ≤ Prob.probability D
      (D.filter fun w => (acquireCompressedFork p m (schedule w)).outcome.isOk) := by
  apply (Prob.sequential_probability_lower D hD _ bounds hd).trans
  apply Prob.probability_mono
  intro w hw
  have hwD := (CryptoBulletproofsIPATreeProbabilityContract.passing_subset D _) hw
  have ht := (Finset.mem_filter.mp hw).2
  have hc := trace_tests_clean p m schedule N w (hn w hwD) ht
  exact Finset.mem_filter.mpr ⟨hwD, (clean_acquisition_exact p m (schedule w) hc).1⟩

omit [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A] in
/-- A path through an origin tree preserves reachability at each sampled step. -/
theorem origin_child_reachable (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (hs : ReachableSnapshot m s) (msg : Packet q A) (st : Statement q A (k + 1))
    (lr : RoundMessages A) (xs : Fin 4 → ZMod q) (ts : Fin 4 → IPATranscriptTree q A k)
    (h : TreeOrigin m s msg (.node st lr xs ts)) (i : Fin 4) :
    ∃ (x : (ZMod q)ˣ) (o : Observation m s (.inner k x)),
      (x : ZMod q) = xs i ∧ ReachableSnapshot m o.after ∧ TreeOrigin m o.after o.packet (ts i) := by
  obtain ⟨x, o, hx, ht⟩ := h.2 i
  exact ⟨x, o, hx, o.reachable hs, ht⟩

structure CryptoHiddenScalarForkAcquisitionContractSuite : Prop where
  acquisition : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (Ω S : Type) (k : ℕ) (p : F.Claim q A k)
    (m : AdversaryModel q A Ω S) ps f,
    (acquireCompressedFork p m ps).outcome = .ok f →
    C.ValidCompressedFork p f ∧ ForkProvenance m f
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (Ω S : Type) (k : ℕ) (p : F.Claim q A k)
    (m : AdversaryModel q A Ω S) ps f,
    (acquireCompressedFork p m ps).outcome = .ok f → F.ResultValid p (C.extractCompressed p f)
  finite_resources : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (Ω S : Type) (k : ℕ) (p : F.Claim q A k)
    (m : AdversaryModel q A Ω S) ps,
    (acquireCompressedFork p m ps).trace.length ≤ scheduleFuel ps

  clean_resources : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (Ω S : Type) (k : ℕ) (p : F.Claim q A k)
    (m : AdversaryModel q A Ω S) ps, Clean (acquireCompressedFork p m ps).trace →
    (acquireCompressedFork p m ps).outcome.isOk = true ∧
    (acquireCompressedFork p m ps).trace.oracleQueries = idealQueries k ∧
    (acquireCompressedFork p m ps).trace.stateRestores = idealQueries k - 1

theorem verification_suite : CryptoHiddenScalarForkAcquisitionContractSuite where
  acquisition := fun _ _ _ _ _ _ _ _ _ => acquire_provenance_and_valid
  extraction := fun _ _ _ _ _ _ _ _ _ => acquire_and_extract_soundness
  finite_resources := fun _ _ _ _ _ _ _ _ _ => acquisition_trace_bound
  clean_resources := fun _ _ _ _ _ _ _ _ _ => clean_acquisition_exact

end CryptoHiddenScalarForkAcquisitionContract
