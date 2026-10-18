/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarInnerProductProtocolContract

/-! Single-path compression and exact postprocessing HVZK. Extraction takes six
supplied accepting trees, not a single transcript or an adversarial rewinding oracle. -/
namespace CryptoHiddenScalarInnerProductCompressionContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
namespace Full
export CryptoHiddenScalarInnerProductProtocolContract
  (Claim Witness WitnessValid Announcement Transcript Verify honestTranscript honest_completeness
   MaskRandomness realView seededSimView real_view_eq_seeded_sim_view honestInteraction
   ValidFork ExtractionResult ResultValid extract three_point_extraction_soundness)
end Full
namespace Public
export CryptoBulletproofsIPAPublicScalarBindingContract
  (PublicClaim toIPA ValidFork extractPair pair_extraction_soundness ClaimResultValid)
end Public
namespace Consistency
export CryptoBulletproofsIPAPedersenOpeningConsistencyContract
  (CommittedClaim liftRelation liftRelation_nonzero liftRelation_eval)
end Consistency
variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A] {k : ℕ}

abbrev Challenges (q k : ℕ) := (ZMod q)ˣ × (Fin k → (ZMod q)ˣ)

structure CompressedTranscript (q : ℕ) (A : Type) (k : ℕ) where
  announcement : Full.Announcement A
  challenge : ZMod q
  product : ZMod q
  blind : ZMod q
  eta : (ZMod q)ˣ
  rounds : Fin k → (ZMod q)ˣ
  proof : IPATranscript q A k

def responseClaim (p : Full.Claim q A k) (ann : Full.Announcement A) (e t : ZMod q) :
    Public.PublicClaim q A k :=
  ⟨p.generators.U, p.generators.G, p.generators.H, ann.mask + e • p.P, t⟩

def scalarCheck (p : Full.Claim q A k) (ann : Full.Announcement A) (e t z : ZMod q) : Prop :=
  t • p.generators.B + z • p.generators.Hblind =
    ann.constant + e • ann.slope + e ^ 2 • p.V

instance [DecidableEq A] (p : Full.Claim q A k) (ann : Full.Announcement A)
    (e t z : ZMod q) : Decidable (scalarCheck p ann e t z) :=
  inferInstanceAs (Decidable (_ = _))

def compressedVerify [DecidableEq A] (p : Full.Claim q A k)
    (tr : CompressedTranscript q A k) : Prop :=
  scalarCheck p tr.announcement tr.challenge tr.product tr.blind ∧
  let s := Public.toIPA (responseClaim p tr.announcement tr.challenge tr.product) tr.eta
  verifier s.U s.G s.H s.P tr.rounds tr.proof = true

instance [DecidableEq A] (p : Full.Claim q A k) (tr : CompressedTranscript q A k) :
    Decidable (compressedVerify p tr) := inferInstanceAs (Decidable (_ ∧ _))

/-- The original witness and its masks are not arguments. -/
def compress (p : Full.Claim q A k) (tr : Full.Transcript q A k) (xs : Challenges q k) :
    CompressedTranscript q A k :=
  ⟨tr.announcement, tr.challenge, dot_product tr.response.left tr.response.right,
   tr.response.blind, xs.1, xs.2,
   prover ((xs.1 : ZMod q) • p.generators.U) p.generators.G p.generators.H
     tr.response.left tr.response.right xs.2⟩

theorem compress_complete [DecidableEq A] (p : Full.Claim q A k)
    (tr : Full.Transcript q A k) (ht : Full.Verify p tr) (xs : Challenges q k) :
    compressedVerify p (compress p tr xs) := by
  refine ⟨ht.2, ?_⟩
  change verifier _ _ _ _ _ (prover _ _ _ _ _ _) = true
  have h := ht.1
  change multiscalar_mul tr.response.left p.generators.G +
    multiscalar_mul tr.response.right p.generators.H = tr.announcement.mask +
      tr.challenge • p.P at h
  simpa only [compress, responseClaim, Public.toIPA, ← h, ipa_target] using
    ipa_completeness ((xs.1 : ZMod q) • p.generators.U) p.generators.G p.generators.H
      tr.response.left tr.response.right xs.2

theorem honest_compressed_complete [DecidableEq A] (p : Full.Claim q A k)
    (w : Full.Witness q k) (hw : Full.WitnessValid p w) (r : Full.MaskRandomness q k)
    (e : ZMod q) (xs : Challenges q k) :
    compressedVerify p (compress p (Full.honestTranscript p w r e) xs) :=
  compress_complete p _ (Full.honest_completeness p w hw r e) xs

/-- Product and blinding responses precede eta and all inner challenges. -/
theorem compression_prefix (p : Full.Claim q A k) (tr : Full.Transcript q A k)
    (xs ys : Challenges q k) :
    (compress p tr xs).announcement = (compress p tr ys).announcement ∧
    (compress p tr xs).challenge = (compress p tr ys).challenge ∧
    (compress p tr xs).product = (compress p tr ys).product ∧
    (compress p tr xs).blind = (compress p tr ys).blind := ⟨rfl, rfl, rfl, rfl⟩

/-- Round j depends on earlier challenges, not challenge j or its future. -/
theorem prover_prefix_causal (U : A) : ∀ {k : ℕ} (G H : Vec k A)
    (a b : Vec k (ZMod q)) (xs ys : Fin k → (ZMod q)ˣ) (j : Fin k),
    (∀ i : Fin k, i.val < j.val → xs i = ys i) →
    (prover U G H a b xs).rounds j = (prover U G H a b ys).rounds j := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ j; exact Fin.elim0 j
  | succ k ih =>
    intro G H a b xs ys j hj
    revert hj
    refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j
    have h0 : xs 0 = ys 0 := hj 0 (by simp)
    simp only [prover, Fin.cons_succ, h0]
    apply ih
    intro i hi
    exact hj i.succ (by simpa using hi)

/-- Independent draws, one at each round. No uniformity is needed for this identity. -/
noncomputable def challengeTape (nu : PMF (ZMod q)ˣ) : (k : ℕ) → PMF (Fin k → (ZMod q)ˣ)
  | 0 => PMF.pure Fin.elim0
  | k + 1 => nu.bind fun x => (challengeTape nu k).map (Fin.cons x)

/-- Operational recursion: construct L,R before drawing x, then recurse on folded state. -/
noncomputable def sequentialIPA (nu : PMF (ZMod q)ˣ) (U : A) :
    {k : ℕ} → (G H : Vec k A) → (a b : Vec k (ZMod q)) →
      PMF ((Fin k → (ZMod q)ˣ) × IPATranscript q A k)
  | 0, _, _, a, b => PMF.pure (Fin.elim0, ⟨Fin.elim0, a 0, b 0⟩)
  | _ + 1, G, H, a, b =>
    let msg := round_messages U G H a b
    nu.bind fun x =>
      (sequentialIPA nu U (fold_generators_G x G) (fold_generators_H x H)
        (fold_vector_a x a) (fold_vector_b x b)).map fun tail =>
          (Fin.cons x tail.1, ⟨Fin.cons msg tail.2.rounds, tail.2.a_final, tail.2.b_final⟩)

theorem sequential_ipa_eq_tape (nu : PMF (ZMod q)ˣ) (U : A) :
    ∀ {k : ℕ} (G H : Vec k A) (a b : Vec k (ZMod q)),
    sequentialIPA nu U G H a b =
      (challengeTape nu k).map (fun xs => (xs, prover U G H a b xs)) := by
  intro k
  induction k with
  | zero => intros; simp [sequentialIPA, challengeTape, PMF.map, prover]
  | succ k ih =>
    intro G H a b
    simp only [sequentialIPA, challengeTape, PMF.map_bind, ih, PMF.map_comp]
    rfl

noncomputable def compressionKernel (p : Full.Claim q A k) (mu : PMF (Challenges q k))
    (tr : Full.Transcript q A k) : PMF (CompressedTranscript q A k) :=
  mu.map (compress p tr)

/-- This theorem permits ANY common law mu, including correlated inner challenges. -/
theorem compressed_hvzk (p : Full.Claim q A k) (w : Full.Witness q k)
    (hw : Full.WitnessValid p w)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind))
    (e : ZMod q) (mu : PMF (Challenges q k)) :
    (Full.realView p w e).bind (compressionKernel p mu) =
      (Full.seededSimView p e).bind (compressionKernel p mu) := by
  rw [Full.real_view_eq_seeded_sim_view p w hw hb e]

noncomputable def independentChallenges (etaLaw innerLaw : PMF (ZMod q)ˣ) (k : ℕ) :
    PMF (Challenges q k) :=
  etaLaw.bind fun eta => (challengeTape innerLaw k).map (fun xs => (eta, xs))

/-- Full response is internal; only product and blind are emitted before eta. -/
noncomputable def sequentialCompression (p : Full.Claim q A k)
    (etaLaw innerLaw : PMF (ZMod q)ˣ) (tr : Full.Transcript q A k) :
    PMF (CompressedTranscript q A k) :=
  let t := dot_product tr.response.left tr.response.right
  let z := tr.response.blind
  etaLaw.bind fun eta =>
    (sequentialIPA innerLaw ((eta : ZMod q) • p.generators.U)
      p.generators.G p.generators.H tr.response.left tr.response.right).map fun tail =>
        ⟨tr.announcement, tr.challenge, t, z, eta, tail.1, tail.2⟩

theorem sequential_compression_eq_kernel (p : Full.Claim q A k)
    (etaLaw innerLaw : PMF (ZMod q)ˣ) (tr : Full.Transcript q A k) :
    sequentialCompression p etaLaw innerLaw tr =
      compressionKernel p (independentChallenges etaLaw innerLaw k) tr := by
  simp only [sequentialCompression, sequential_ipa_eq_tape, compressionKernel,
    independentChallenges, PMF.map_bind, PMF.map_comp]
  rfl

noncomputable def honestExecution (p : Full.Claim q A k) (w : Full.Witness q k)
    (outerLaw : PMF (ZMod q)) (etaLaw innerLaw : PMF (ZMod q)ˣ) :
    PMF (CompressedTranscript q A k) :=
  (PMF.uniformOfFintype (Full.MaskRandomness q k)).bind fun r =>
    outerLaw.bind fun e =>
      sequentialCompression p etaLaw innerLaw (Full.honestTranscript p w r e)

theorem honest_execution_eq_postprocessing (p : Full.Claim q A k) (w : Full.Witness q k)
    (outerLaw : PMF (ZMod q)) (etaLaw innerLaw : PMF (ZMod q)ˣ) :
    honestExecution p w outerLaw etaLaw innerLaw =
      (Full.honestInteraction p w outerLaw).bind
        (compressionKernel p (independentChallenges etaLaw innerLaw k)) := by
  simp only [honestExecution, Full.honestInteraction, PMF.bind_bind, PMF.bind_map,
    Function.comp_def, sequential_compression_eq_kernel]

/-- A simulator law, with no witness argument and no blinding-map inversion. -/
noncomputable def simulatedExecution (p : Full.Claim q A k) (outerLaw : PMF (ZMod q))
    (mu : PMF (Challenges q k)) : PMF (CompressedTranscript q A k) :=
  outerLaw.bind fun e => (Full.seededSimView p e).bind (compressionKernel p mu)

theorem execution_hvzk (p : Full.Claim q A k) (w : Full.Witness q k)
    (hw : Full.WitnessValid p w)
    (hb : Function.Bijective (fun x : ZMod q => x • p.generators.Hblind))
    (outerLaw : PMF (ZMod q)) (etaLaw innerLaw : PMF (ZMod q)ˣ) :
    honestExecution p w outerLaw etaLaw innerLaw =
      simulatedExecution p outerLaw (independentChallenges etaLaw innerLaw k) := by
  rw [honest_execution_eq_postprocessing]
  have h : Full.honestInteraction p w outerLaw = outerLaw.bind (Full.realView p w) :=
    PMF.bind_comm _ _ _
  rw [h, PMF.bind_bind]
  simp only [simulatedExecution, compressed_hvzk p w hw hb]

structure ForkNode (q : ℕ) (A : Type) (k : ℕ) where
  challenge : ZMod q
  product : ZMod q
  blind : ZMod q
  eta₀ : (ZMod q)ˣ
  eta₁ : (ZMod q)ˣ
  tree₀ : IPATranscriptTree q A k
  tree₁ : IPATranscriptTree q A k

structure CompressedFork (q : ℕ) (A : Type) (k : ℕ) where
  announcement : Full.Announcement A
  nodes : Fin 3 → ForkNode q A k

def ValidCompressedFork (p : Full.Claim q A k) (f : CompressedFork q A k) : Prop :=
  Function.Injective (fun i => (f.nodes i).challenge) ∧ ∀ i,
    scalarCheck p f.announcement (f.nodes i).challenge (f.nodes i).product (f.nodes i).blind ∧
    Public.ValidFork (responseClaim p f.announcement (f.nodes i).challenge (f.nodes i).product)
      (f.nodes i).eta₀ (f.nodes i).eta₁ (f.nodes i).tree₀ (f.nodes i).tree₁

instance [DecidableEq A] (p : Full.Claim q A k) (f : CompressedFork q A k) :
    Decidable (ValidCompressedFork p f) := inferInstanceAs (Decidable (_ ∧ ∀ _, _ ∧ _))

def nodeResult (p : Full.Claim q A k) (f : CompressedFork q A k) (i : Fin 3) :
    TreeExtractionResult q k :=
  Public.extractPair (responseClaim p f.announcement (f.nodes i).challenge (f.nodes i).product)
    (f.nodes i).eta₀ (f.nodes i).eta₁ (f.nodes i).tree₀ (f.nodes i).tree₁

def recovered (f : CompressedFork q A k) (a b : Fin 3 → Vec k (ZMod q)) :
    Fin 3 → Full.Transcript q A k := fun i =>
  ⟨f.announcement, (f.nodes i).challenge, ⟨a i, b i, (f.nodes i).blind⟩⟩

theorem recovered_fork_valid (p : Full.Claim q A k) (f : CompressedFork q A k)
    (hf : ValidCompressedFork p f) (a b : Fin 3 → Vec k (ZMod q))
    (hr : ∀ i, nodeResult p f i = .witness (a i) (b i)) :
    Full.ValidFork p (recovered f a b) := by
  refine ⟨?_, fun _ => rfl, hf.1⟩
  intro i
  have h := Public.pair_extraction_soundness _ _ _ _ _ (hf.2 i).2
  change Public.ClaimResultValid _ (nodeResult p f i) at h
  rw [hr i] at h
  refine ⟨h.1.symm, ?_⟩
  change dot_product (a i) (b i) • _ + _ = _
  rw [h.2]
  exact (hf.2 i).1

/-- Deterministic priority: first internal relation, otherwise the outer extractor. -/
def extractCompressed (p : Full.Claim q A k) (f : CompressedFork q A k) :
    Full.ExtractionResult q k :=
  let rs := nodeResult p f
  if h : ∃ i, isRelation (rs i) = true then
    .relation (Consistency.liftRelation (coefficients (rs (Fin.find _ h))))
  else Full.extract (recovered f (fun i => witnessA (rs i)) (fun i => witnessB (rs i)))

theorem compressed_extraction_soundness (p : Full.Claim q A k) (f : CompressedFork q A k)
    (hf : ValidCompressedFork p f) : Full.ResultValid p (extractCompressed p f) := by
  have hs : ∀ i, Public.ClaimResultValid
      (responseClaim p f.announcement (f.nodes i).challenge (f.nodes i).product)
      (nodeResult p f i) := fun i => Public.pair_extraction_soundness _ _ _ _ _ (hf.2 i).2
  unfold extractCompressed
  dsimp only
  split_ifs with h
  · have hh := Fin.find_spec h
    have hv := hs (Fin.find _ h)
    cases he : nodeResult p f (Fin.find _ h) with
    | witness a b =>
      rw [he] at hh
      exact Bool.noConfusion hh
    | relation d =>
      rw [he] at hv
      change Consistency.liftRelation d ≠ 0 ∧ _
      refine ⟨Consistency.liftRelation_nonzero d hv.1, ?_⟩
      exact (Consistency.liftRelation_eval
        ⟨p.generators, f.announcement.mask + (f.nodes (Fin.find _ h)).challenge • p.P, p.V⟩
        (f.nodes (Fin.find _ h)).product d).trans hv.2
  · apply Full.three_point_extraction_soundness
    apply recovered_fork_valid p f hf
    intro i
    cases he : nodeResult p f i with
    | witness a b => rfl
    | relation d => exact False.elim (h ⟨i, by simp [he, isRelation]⟩)

def checkedExtract [DecidableEq A] (p : Full.Claim q A k) (f : CompressedFork q A k) :
    Option (Full.ExtractionResult q k) :=
  if ValidCompressedFork p f then some (extractCompressed p f) else none

theorem checked_extract_success_iff [DecidableEq A] (p : Full.Claim q A k)
    (f : CompressedFork q A k) :
    (checkedExtract p f).isSome = true ↔ ValidCompressedFork p f := by
  simp only [checkedExtract]; split_ifs <;> simp_all

theorem checked_extract_sound [DecidableEq A] (p : Full.Claim q A k)
    (f : CompressedFork q A k) (r : Full.ExtractionResult q k)
    (h : checkedExtract p f = some r) : Full.ResultValid p r := by
  unfold checkedExtract at h
  split_ifs at h with hf
  · cases h; exact compressed_extraction_soundness p f hf

/-- Honest trees for a supplied full response; used for completeness, not acquisition. -/
def nodeFromFull (p : Full.Claim q A k) (tr : Full.Transcript q A k)
    (u : Fin 4 → (ZMod q)ˣ) (eta₀ eta₁ : (ZMod q)ˣ) : ForkNode q A k :=
  ⟨tr.challenge, dot_product tr.response.left tr.response.right, tr.response.blind, eta₀, eta₁,
   honestTree u ((eta₀ : ZMod q) • p.generators.U) p.generators.G p.generators.H
     tr.response.left tr.response.right,
   honestTree u ((eta₁ : ZMod q) • p.generators.U) p.generators.G p.generators.H
     tr.response.left tr.response.right⟩

def forkFromFull (p : Full.Claim q A k) (f : Fin 3 → Full.Transcript q A k)
    (u : Fin 4 → (ZMod q)ˣ) (eta₀ eta₁ : (ZMod q)ˣ) : CompressedFork q A k :=
  ⟨(f 0).announcement, fun i => nodeFromFull p (f i) u eta₀ eta₁⟩

theorem fork_from_full_valid (p : Full.Claim q A k) (f : Fin 3 → Full.Transcript q A k)
    (hf : Full.ValidFork p f) (u : Fin 4 → (ZMod q)ˣ)
    (hu : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (eta₀ eta₁ : (ZMod q)ˣ) (he : eta₀ ≠ eta₁) :
    ValidCompressedFork p (forkFromFull p f u eta₀ eta₁) := by
  refine ⟨hf.2.2, ?_⟩
  intro i
  have hctx (eta : (ZMod q)ˣ) :
      Public.toIPA (responseClaim p (f 0).announcement (f i).challenge
        (dot_product (f i).response.left (f i).response.right)) eta =
      witness_statement ((eta : ZMod q) • p.generators.U) p.generators.G p.generators.H
        (f i).response.left (f i).response.right := by
    have h := (hf.1 i).1
    change multiscalar_mul _ _ + multiscalar_mul _ _ = _ at h
    simp only [Public.toIPA, responseClaim, witness_statement, ipa_target, hf.2.1 i] at *
    rw [h]
  constructor
  · change scalarCheck p (f 0).announcement (f i).challenge _ _
    rw [← hf.2.1 i]
    exact (hf.1 i).2
  · refine ⟨he, ?_, ?_⟩
    · change ValidAcceptingTree _ (honestTree u _ _ _ _ _)
      dsimp only [forkFromFull, nodeFromFull]
      rw [hctx]
      exact honestTree_valid u hu _ _ _ _ _
    · change ValidAcceptingTree _ (honestTree u _ _ _ _ _)
      dsimp only [forkFromFull, nodeFromFull]
      rw [hctx]
      exact honestTree_valid u hu _ _ _ _ _

theorem fork_from_full_node_result (p : Full.Claim q A k)
    (f : Fin 3 → Full.Transcript q A k) (u : Fin 4 → (ZMod q)ˣ)
    (hu : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (eta₀ eta₁ : (ZMod q)ˣ) (i : Fin 3) :
    nodeResult p (forkFromFull p f u eta₀ eta₁) i =
      .witness (f i).response.left (f i).response.right := by
  simp [nodeResult, forkFromFull, nodeFromFull, Public.extractPair,
    honestTree_exact u (hu.ne (by decide)),
    CryptoBulletproofsIPAPublicScalarBindingContract.combineResults,
    CryptoBulletproofsIPAPublicScalarBindingContract.difference, responseClaim]

theorem extract_from_full (p : Full.Claim q A k) (f : Fin 3 → Full.Transcript q A k)
    (hf : Full.ValidFork p f) (u : Fin 4 → (ZMod q)ˣ)
    (hu : Function.Injective (fun i => (u i : ZMod q) ^ 2)) (eta₀ eta₁ : (ZMod q)ˣ) :
    extractCompressed p (forkFromFull p f u eta₀ eta₁) = Full.extract f := by
  simp only [extractCompressed, fork_from_full_node_result p f u hu, isRelation,
    Bool.false_eq_true, exists_false, ↓reduceDIte, witnessA, witnessB]
  congr 1
  funext i
  change (⟨(f 0).announcement, (f i).challenge,
    ⟨(f i).response.left, (f i).response.right, (f i).response.blind⟩⟩ :
      Full.Transcript q A k) = f i
  rw [← hf.2.1 i]

omit [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] in
/-- Reuses the existing count: two group elements per IPA round and two final scalars. -/
theorem compressed_payload (tr : CompressedTranscript q A k) :
    (group_payload tr.proof).length + 3 = 2 * k + 3 ∧
    (scalar_payload tr.proof).length + 2 = 4 := by
  obtain ⟨_, hg, hs⟩ := ipa_proof_elements_count tr.proof
  exact ⟨by omega, by omega⟩

/-- Each path of a supplied valid tree is an accepted single compressed execution. -/
theorem accepting_tree_compression [DecidableEq A] (p : Full.Claim q A k)
    (ann : Full.Announcement A) (e t z : ZMod q) (eta : (ZMod q)ˣ)
    (tree : IPATranscriptTree q A k) (path : Fin k → Fin 4) (xs : Fin k → (ZMod q)ˣ)
    (hs : scalarCheck p ann e t z)
    (ht : ValidAcceptingTree (Public.toIPA (responseClaim p ann e t) eta) tree)
    (hm : PathMatches tree path xs) :
    compressedVerify p ⟨ann, e, t, z, eta, xs, path_transcript tree path⟩ :=
  ⟨hs, accepting_path_verifier _ tree path xs ht hm⟩

/-- Executable simulation from field-valued seeds; no inverse or witness is used. -/
def seededCompressedSimulator (p : Full.Claim q A k) (e : ZMod q)
    (r : Full.MaskRandomness q k) (xs : Challenges q k) : CompressedTranscript q A k :=
  compress p (CryptoHiddenScalarInnerProductProtocolContract.seededSimulator p e r) xs

theorem seeded_compressed_accepts [DecidableEq A] (p : Full.Claim q A k) (e : ZMod q)
    (r : Full.MaskRandomness q k) (xs : Challenges q k) :
    compressedVerify p (seededCompressedSimulator p e r xs) :=
  compress_complete p _ (CryptoHiddenScalarInnerProductProtocolContract.simulator_accepts p e _) xs

noncomputable def uniformChallenges (q k : ℕ) [Fact q.Prime] : PMF (Challenges q k) :=
  independentChallenges (PMF.uniformOfFintype _) (PMF.uniformOfFintype _) k

structure CryptoHiddenScalarInnerProductCompressionContractSuite : Prop where
  completeness : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (p : Full.Claim q A k) (tr : Full.Transcript q A k),
    Full.Verify p tr → ∀ xs, compressedVerify p (compress p tr xs)
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (p : Full.Claim q A k) (f : CompressedFork q A k),
    ValidCompressedFork p f → Full.ResultValid p (extractCompressed p f)
  hvzk : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (p : Full.Claim q A k) (w : Full.Witness q k), Full.WitnessValid p w →
    Function.Bijective (fun x : ZMod q => x • p.generators.Hblind) →
    ∀ e mu, (Full.realView p w e).bind (compressionKernel p mu) =
      (Full.seededSimView p e).bind (compressionKernel p mu)
  execution : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (p : Full.Claim q A k) (w : Full.Witness q k) outer eta inner,
    honestExecution p w outer eta inner = (Full.honestInteraction p w outer).bind
      (compressionKernel p (independentChallenges eta inner k))

theorem verification_suite : CryptoHiddenScalarInnerProductCompressionContractSuite where
  completeness := fun _ _ _ _ _ _ _ => compress_complete
  extraction := fun _ _ _ _ _ _ => compressed_extraction_soundness
  hvzk := fun _ _ _ _ _ _ => compressed_hvzk
  execution := fun _ _ _ _ _ _ => honest_execution_eq_postprocessing

end CryptoHiddenScalarInnerProductCompressionContract
