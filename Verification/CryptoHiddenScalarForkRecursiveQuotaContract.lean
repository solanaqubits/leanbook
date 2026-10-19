/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarForkLocalDensityContract

/-! Bottom-up bounds for the actual snapshot collector. Finite uniform microseeds,
common seed shape/budget at each depth, snapshot-dependent call decoders. No supplied
child success bounds, new collector, global-acceptance, ROM or complexity claim. -/
namespace CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkScheduleProgressContract
open CryptoHiddenScalarForkLocalDensityContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction

/-- Finite microseed law; key fibers, not individual calls, control collisions. -/
structure CallLaw (S U K : Type) [DecidableEq K] (key : U → K) where
  size : ℕ
  size_pos : 0 < size
  call : S → Fin size → U
  beta : ℚ
  beta_nonneg : 0 ≤ beta
  mass : ∀ s a, Prob.probability (Finset.univ : Finset (Fin size))
    (Finset.univ.filter fun i => key (call s i) = a) ≤ beta

def quota (n T : ℕ) (d beta : ℚ) : ℚ :=
  quotaLower n (fun j => max 0 (d - (j : ℚ) * beta)) T 0

theorem quota_range (n T : ℕ) (d beta : ℚ) (hd : 0 ≤ d ∧ d ≤ 1) (hb : 0 ≤ beta) :
    0 ≤ quota n T d beta ∧ quota n T d beta ≤ 1 := by
  apply quota_bounds
  intro j _
  exact ⟨le_max_left _ _, max_le (by norm_num)
    (le_trans (sub_le_self d (mul_nonneg (Nat.cast_nonneg _) hb)) hd.2)⟩

@[simp] theorem tapes_univ {U : Type} [Fintype U] (T : ℕ) :
    Product.productTapes (Finset.univ : Finset U) T = Finset.univ := by
  ext w
  simp [Product.productTapes]

/-- A failed primitive transition has no child; this fallback is used only to
supply an unused schedule on that failed branch. -/
def afterQuery {q : ℕ} {A Ω S : Type} (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (req : Request q) : Snapshot q S :=
  (query m s req).elim s (fun o => o.after)

/-- Uniform seed shape by depth, with calls allowed to depend on the full snapshot. -/
inductive TreePlan (q : ℕ) (S : Type) : ℕ → Type where
  | leaf : TreePlan q S 0
  | node {d : ℕ}
      (law : CallLaw (Snapshot q S) (ZMod q)ˣ (ZMod q) (fun x => (x : ZMod q)^2))
      (budget : ℕ) (child : TreePlan q S d) : TreePlan q S (d + 1)

namespace TreePlan

def Seed {q : ℕ} {S : Type} : {d : ℕ} → TreePlan q S d → Type
  | _, .leaf => Unit
  | _, .node law T child => Fin T → Fin law.size × Seed child

instance seedFintype {q : ℕ} {S : Type} : {d : ℕ} → (p : TreePlan q S d) → Fintype p.Seed
  | _, .leaf => inferInstanceAs (Fintype Unit)
  | _, .node law T child => letI := seedFintype child
                           inferInstanceAs (Fintype (Fin T → Fin law.size × child.Seed))

instance seedDecidableEq {q : ℕ} {S : Type} : {d : ℕ} → (p : TreePlan q S d) → DecidableEq p.Seed
  | _, .leaf => inferInstanceAs (DecidableEq Unit)
  | _, .node law T child => letI := seedDecidableEq child
                           inferInstanceAs (DecidableEq (Fin T → Fin law.size × child.Seed))

instance seedNonempty {q : ℕ} {S : Type} {d : ℕ} (p : TreePlan q S d) : Nonempty p.Seed := by
  induction p with
  | leaf => exact ⟨()⟩
  | node law T child ih =>
    obtain ⟨v⟩ := ih
    exact ⟨fun _ => (⟨0, law.size_pos⟩,v)⟩

variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
  [DecidableEq A] {Ω S : Type}

/-- Pure schedule decoder. Primitive queries are deterministic model evaluation;
they do not create a second ResourceTrace or a second acquisition algorithm. -/
def decode (m : AdversaryModel q A Ω S) : {d : ℕ} → (p : TreePlan q S d) →
    Snapshot q S → p.Seed → IPASchedule q d
  | _, .leaf, _, _ => ()
  | d + 1, .node law _T child, s, w => iidSchedule (fun uv =>
      let x := law.call s uv.1
      let s' := afterQuery m s (.inner d x)
      (x, decode m child s' uv.2)) w

/-- Leaves use the real verifier, including malformed packets. -/
def bound : {d : ℕ} → TreePlan q S d → AdversaryModel q A Ω S →
    Snapshot q S → Packet q A → Statement q A d → ℚ
  | 0, .leaf, _, _, msg, st => match msg with
    | .leaf a b => if ValidAcceptingTree st (.leaf st a b) then 1 else 0
    | _ => 0
  | d + 1, .node law T child, m, s, msg, st => match msg with
    | .round lr => quota 4 T
        (average Finset.univ (fun i => (query m s (.inner d (law.call s i))).elim 0
          (fun o => bound child m o.after o.packet
            (child_statement st lr (law.call s i))))) law.beta
    | _ => 0

theorem bound_range {d : ℕ} (p : TreePlan q S d) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (msg : Packet q A) (st : Statement q A d) :
    0 ≤ bound p m s msg st ∧ bound p m s msg st ≤ 1 := by
  induction p generalizing s msg with
  | leaf => cases msg <;> simp only [bound] <;> (try split_ifs) <;> norm_num
  | @node d law T child ih =>
    cases msg <;> try { simp [bound] }
    rename_i lr
    apply quota_range
    · apply average_bounds
      · exact ⟨⟨0, law.size_pos⟩, Finset.mem_univ _⟩
      · intro i _
        cases hq : query m s (.inner d (law.call s i)) <;> simp only [Option.elim]
        · norm_num
        · exact ih _ _ _
    · exact law.beta_nonneg

set_option backward.isDefEq.respectTransparency false in
/-- No child probability hypotheses: the induction starts at the actual leaf check. -/
theorem probability_lower {d : ℕ} (p : TreePlan q S d) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (msg : Packet q A) (st : Statement q A d) :
    bound p m s msg st ≤ Prob.probability (Finset.univ : Finset p.Seed)
      (Finset.univ.filter fun w => (acquireTree m s hs msg st (decode m p s w)).value.isSome) := by
  induction p generalizing s msg with
  | leaf =>
    cases msg <;> simp [bound, acquireTree, failed, Prob.probability]
    split_ifs <;> simp_all
  | @node d law T child ih =>
    cases msg <;> try { simp [bound, acquireTree, failed, Prob.probability] }
    rename_i lr
    let C : Finset (Fin law.size) := Finset.univ
    let D : Finset child.Seed := Finset.univ
    let b := fun i => (query m s (.inner d (law.call s i))).elim (0 : ℚ)
      (fun o => bound child m o.after o.packet (child_statement st lr (law.call s i)))
    let ch := fun i v => decode m child
      (afterQuery m s (.inner d (law.call s i))) v
    have hc : C.Nonempty := ⟨⟨0,law.size_pos⟩, Finset.mem_univ _⟩
    have hd : D.Nonempty := Finset.univ_nonempty
    have br : ∀ i ∈ C, 0 ≤ b i ∧ b i ≤ 1 := by
      intro i _
      dsimp [b]
      cases hq : query m s (.inner d (law.call s i)) <;> simp only [Option.elim]
      · norm_num
      · apply bound_range
    have lower : ∀ i ∈ C, b i ≤ roundChildRate m s hs st lr D (law.call s i) (ch i) := by
      intro i _
      unfold b roundChildRate ch afterQuery
      cases hq : query m s (.inner d (law.call s i)) <;> simp only [Option.elim]
      · exact le_rfl
      · exact ih _ _ _ _
    have h := iid_tree_probability_lower m s hs st lr (C ×ˢ D) (hc.product hd)
      (fun uv => (law.call s uv.1,ch uv.1 uv.2)) (average C b) law.beta
      (average_bounds C hc b br).1 (average_bounds C hc b br).2 law.beta_nonneg
      (round_density_lower m s hs st lr C D (law.call s) ch b lower) (by
        intro a
        rw [full_probe_class_mass_eq C D hd (fun i v => (law.call s i, ch i v))
          (fun pr => (pr.1 : ZMod q)^2)
          (fun i => (law.call s i : ZMod q)^2) (fun _ _ => rfl) a]
        exact law.mass s a) T
    convert h using 1 <;>
      simp only [C,D,Finset.univ_product_univ,tapes_univ,bound,decode,quota,b,ch]
    all_goals congr! 12

end TreePlan

/-- Eta quota law and the concrete recursive IPA law used below it. -/
structure EtaPlan (q : ℕ) (S : Type) (k : ℕ) where
  law : CallLaw (Snapshot q S) (ZMod q)ˣ (ZMod q)ˣ id
  budget : ℕ
  tree : TreePlan q S k

namespace EtaPlan
abbrev Seed {q k : ℕ} {S : Type} (p : EtaPlan q S k) :=
  Fin p.budget → Fin p.law.size × p.tree.Seed
instance {q k : ℕ} {S : Type} (p : EtaPlan q S k) : Nonempty p.Seed :=
  ⟨fun _ => (⟨0,p.law.size_pos⟩, Classical.choice inferInstance)⟩

variable {q k : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
  [DecidableEq A] {Ω S : Type}

def decode (p : EtaPlan q S k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (w : p.Seed) : EtaSchedule q k :=
  iidSchedule (fun uv =>
    let eta := p.law.call s uv.1
    let s' := afterQuery m s (.binding eta)
    (eta,p.tree.decode m s' uv.2)) w

def branch (p : EtaPlan q S k) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (ann : F.Announcement A) (e t : ZMod q) (i : Fin p.law.size) : ℚ :=
  match query m s (.binding (p.law.call s i)) with
  | none => 0
  | some o => p.tree.bound m o.after o.packet
      (P.toIPA (C.responseClaim claim ann e t) (p.law.call s i))

def bound (p : EtaPlan q S k) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (ann : F.Announcement A) (e t : ZMod q) : ℚ :=
  quota 2 p.budget (average Finset.univ (p.branch claim m s ann e t)) p.law.beta

theorem branch_range (p : EtaPlan q S k) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (ann : F.Announcement A) (e t : ZMod q) (i : Fin p.law.size) :
    0 ≤ p.branch claim m s ann e t i ∧ p.branch claim m s ann e t i ≤ 1 := by
  unfold branch; split
  · norm_num
  · exact TreePlan.bound_range _ _ _ _ _

theorem bound_range (p : EtaPlan q S k) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (ann : F.Announcement A) (e t : ZMod q) :
    0 ≤ p.bound claim m s ann e t ∧ p.bound claim m s ann e t ≤ 1 := by
  apply quota_range
  · exact average_bounds _ ⟨⟨0,p.law.size_pos⟩,Finset.mem_univ _⟩ _
      (fun i _ => branch_range p claim m s ann e t i)
  · exact p.law.beta_nonneg

/-- The eta bound concerns the actual existing collect loop, at its exact post-e snapshot. -/
theorem probability_lower (p : EtaPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (ann : F.Announcement A) (e t : ZMod q) :
    p.bound claim m s ann e t ≤ Prob.probability (Finset.univ : Finset p.Seed)
      (Finset.univ.filter fun w => (collect 2 Prod.fst (fun v => v.1)
        (etaAttempt claim m s hs ann e t) (p.decode m s w)).value.isSome) := by
  let U : Finset (Fin p.law.size) := Finset.univ
  let D : Finset p.tree.Seed := Finset.univ
  let ch := fun i v => p.tree.decode m
    (afterQuery m s (.binding (p.law.call s i))) v
  have hu : U.Nonempty := ⟨⟨0,p.law.size_pos⟩,Finset.mem_univ _⟩
  have hd : D.Nonempty := Finset.univ_nonempty
  have lower : ∀ i ∈ U, p.branch claim m s ann e t i ≤
      etaChildRate claim m s hs ann e t D (p.law.call s i) (ch i) := by
    intro i _
    unfold branch etaChildRate ch afterQuery
    split <;> rename_i h
    · simp [h]
    · simpa only [h, D, Option.elim] using TreePlan.probability_lower p.tree m _ _ _ _
  have h := iid_collect_probability_lower 2 (U ×ˢ D) (hu.product hd)
    (fun uv => (p.law.call s uv.1,ch uv.1 uv.2)) Prod.fst (fun v => v.1)
    (etaAttempt claim m s hs ann e t) (eta_key_coherent claim m s hs ann e t)
    (average U (p.branch claim m s ann e t)) p.law.beta
    (average_bounds U hu _ (fun i _ => branch_range p claim m s ann e t i)).1
    (average_bounds U hu _ (fun i _ => branch_range p claim m s ann e t i)).2 p.law.beta_nonneg
    (eta_density_lower claim m s hs ann e t U D (p.law.call s) ch _ lower) (by
      intro a
      rw [full_probe_class_mass_eq U D hd (fun i v => (p.law.call s i,ch i v)) Prod.fst
        (p.law.call s) (fun _ _ => rfl) a]
      exact p.law.mass s a) p.budget
  convert h using 1 <;> simp only [U,D,Finset.univ_product_univ,tapes_univ,bound,quota,decode,ch]
  all_goals congr! 12
end EtaPlan

/-- Outer quota law; no supplied internal probability estimates. -/
structure ProtocolPlan (q : ℕ) (S : Type) (k : ℕ) where
  law : CallLaw (Snapshot q S) (ZMod q) (ZMod q) id
  budget : ℕ
  eta : EtaPlan q S k

namespace ProtocolPlan
abbrev Seed {q k : ℕ} {S : Type} (p : ProtocolPlan q S k) :=
  Fin p.budget → Fin p.law.size × p.eta.Seed
instance {q k : ℕ} {S : Type} (p : ProtocolPlan q S k) : Nonempty p.Seed :=
  ⟨fun _ => (⟨0,p.law.size_pos⟩, Classical.choice inferInstance)⟩

variable {q k : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
  [DecidableEq A] {Ω S : Type}

def decodeAt (p : ProtocolPlan q S k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (w : p.Seed) : ProbeSchedule q k :=
  iidSchedule (fun uv =>
    let e := p.law.call s uv.1
    let s' := afterQuery m s (.outer e)
    (e,p.eta.decode m s' uv.2)) w

def decode (p : ProtocolPlan q S k) (m : AdversaryModel q A Ω S) (w : p.Seed) : ProbeSchedule q k :=
  p.decodeAt m (afterQuery m (initialSnapshot m) .commit) w

def branch (p : ProtocolPlan q S k) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (ann : F.Announcement A) (i : Fin p.law.size) : ℚ :=
  match query m s (.outer (p.law.call s i)) with
  | none => 0
  | some o => match o.packet with
    | .scalar t z => if C.scalarCheck claim ann (p.law.call s i) t z then
        p.eta.bound claim m o.after ann (p.law.call s i) t else 0
    | _ => 0

def boundAt (p : ProtocolPlan q S k) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (ann : F.Announcement A) : ℚ :=
  quota 3 p.budget (average Finset.univ (p.branch claim m s ann)) p.law.beta

def bound (p : ProtocolPlan q S k) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S) : ℚ :=
  match query m (initialSnapshot m) .commit with
  | none => 0
  | some o => match o.packet with
    | .announcement ann => p.boundAt claim m o.after ann
    | _ => 0

theorem branch_range (p : ProtocolPlan q S k) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (ann : F.Announcement A) (i : Fin p.law.size) :
    0 ≤ p.branch claim m s ann i ∧ p.branch claim m s ann i ≤ 1 := by
  unfold branch
  split
  · norm_num
  · split <;> try { norm_num }
    split_ifs
    · apply EtaPlan.bound_range
    · norm_num

theorem bound_range (p : ProtocolPlan q S k) (claim : F.Claim q A k) (m : AdversaryModel q A Ω S) :
    0 ≤ p.bound claim m ∧ p.bound claim m ≤ 1 := by
  unfold bound
  split
  · norm_num
  · split <;> try { norm_num }
    apply quota_range
    · exact average_bounds _ ⟨⟨0,p.law.size_pos⟩,Finset.mem_univ _⟩ _
        (fun i _ => branch_range p claim m _ _ i)
    · exact p.law.beta_nonneg

set_option backward.isDefEq.respectTransparency false in
theorem probability_lower (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) :
    p.bound claim m ≤ Prob.probability (Finset.univ : Finset p.Seed)
      (Finset.univ.filter fun w =>
        (acquireCompressedFork claim m (p.decode m w)).outcome.isOk) := by
  unfold bound
  split
  · exact CryptoBulletproofsIPATreeProbabilityContract.probability_nonnegative _ _
  · rename_i o ho
    split
    · rename_i ann ha
      let U : Finset (Fin p.law.size) := Finset.univ
      let D : Finset p.eta.Seed := Finset.univ
      let ch := fun i v => p.eta.decode m
        (afterQuery m o.after (.outer (p.law.call o.after i))) v
      have lower : ∀ i ∈ U, p.branch claim m o.after ann i ≤
          outerChildRate claim m o.after (o.reachable .initial) ann D (p.law.call o.after i)
            (ch i) := by
        intro i _
        unfold branch outerChildRate ch afterQuery
        split <;> rename_i h
        · simp [h]
        · simp only [h, Option.elim]
          split <;> rename_i hp
          · simp only [hp]
            split_ifs
            · exact p.eta.probability_lower claim m _ _ ann _ _
            · exact le_rfl
          · split <;> simp_all
      have h := averaged_acquisition_probability_lower claim m o ann ho ha U
        ⟨⟨0,p.law.size_pos⟩,Finset.mem_univ _⟩ D Finset.univ_nonempty (p.law.call o.after) ch
        (p.branch claim m o.after ann) (fun i _ => branch_range p claim m o.after ann i) lower
        p.law.beta p.law.beta_nonneg (p.law.mass o.after) p.budget
      have hinit : afterQuery m (initialSnapshot m) .commit = o.after := by simp [afterQuery,ho]
      simpa only [U,D,Finset.univ_product_univ,tapes_univ,boundAt,quota,decode,hinit,
        decodeAt,ch] using h
    · exact CryptoBulletproofsIPATreeProbabilityContract.probability_nonnegative _ _

/-- Positive computed bottom-up bound gives a real acquired fork, provenance and extraction. -/
theorem positive_extracts (p : ProtocolPlan q S k) (claim : F.Claim q A k)
    (m : AdversaryModel q A Ω S) (h : 0 < p.bound claim m) :
    ∃ w : p.Seed, ∃ f, (acquireCompressedFork claim m (p.decode m w)).outcome = .ok f ∧
      ForkProvenance m f ∧ F.ResultValid claim (C.extractCompressed claim f) := by
  obtain ⟨w,_,f,hf,hp,he⟩ := positive_schedule_probability_extracts claim m Finset.univ
    (p.decode m) (lt_of_lt_of_le h (p.probability_lower claim m))
  exact ⟨w,f,hf,hp,he⟩
end ProtocolPlan


structure CryptoHiddenScalarForkRecursiveQuotaContractSuite : Prop where
  tree_probability : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S : Type) (k : ℕ) (p : TreePlan q S k)
    (m : AdversaryModel q A Ω S) (s : Snapshot q S) (hs : ReachableSnapshot m s)
    (msg : Packet q A) (st : Statement q A k),
    p.bound m s msg st ≤ Prob.probability Finset.univ
      (Finset.univ.filter fun w => (acquireTree m s hs msg st (p.decode m s w)).value.isSome)
  protocol_probability : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S : Type) (k : ℕ) (p : ProtocolPlan q S k)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S),
    p.bound claim m ≤ Prob.probability Finset.univ
      (Finset.univ.filter fun w => (acquireCompressedFork claim m (p.decode m w)).outcome.isOk)
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (Ω S : Type) (k : ℕ) (p : ProtocolPlan q S k)
    (claim : F.Claim q A k) (m : AdversaryModel q A Ω S), 0 < p.bound claim m →
    ∃ w : p.Seed, ∃ f, (acquireCompressedFork claim m (p.decode m w)).outcome = .ok f ∧
      ForkProvenance m f ∧ F.ResultValid claim (C.extractCompressed claim f)

theorem verification_suite : CryptoHiddenScalarForkRecursiveQuotaContractSuite where
  tree_probability := fun _ _ _ _ _ _ _ _ _ => TreePlan.probability_lower
  protocol_probability := fun _ _ _ _ _ _ _ _ _ => ProtocolPlan.probability_lower
  extraction := fun _ _ _ _ _ _ _ _ _ => ProtocolPlan.positive_extracts

end CryptoHiddenScalarForkRecursiveQuotaContract
