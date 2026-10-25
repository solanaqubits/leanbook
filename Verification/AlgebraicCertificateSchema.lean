/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.AlgebraicCertificateSyntax
import Verification.AlgebraicCertificateKernel

/-!
# ALCC-SCHEMA-DECODE-1

Independent structural relations and proof-producing, executable AST decoders.
No byte parser, SHA-256 computation, hash equality or external Python refinement.
The result is an unbound task; successful decoding is not certificate acceptance.
-/
namespace AlgebraicCertificateSchema
open AlgebraicCertificateSyntax AlgebraicCertificateKernel

/-- ASCII constants used only for field names and profile literals. -/
def bytes (s : String) : Bytes := s.toUTF8.toList

/-- Exact positional object shape, independent of any decoder. -/
inductive FieldsRel (keys : List Bytes) : JsonAST → List JsonAST → Prop where
  | intro (fs : List (Bytes × JsonAST)) (hk : fs.map Prod.fst = keys) :
      FieldsRel keys (.object fs) (fs.map Prod.snd)

/-- A proof-producing decoder. Proofs are erased by compilation. -/
abbrev Checked {α : Type} (r : JsonAST → α → Prop) :=
  (j : JsonAST) → Option { a : α // r j a }

def fields (keys : List Bytes) : Checked (FieldsRel keys)
  | .object fs => if h : fs.map Prod.fst = keys then
      some ⟨fs.map Prod.snd, .intro fs h⟩ else none
  | _ => none

theorem fields_unique {ks : List Bytes} {j : JsonAST} {a b : List JsonAST}
    (ha : FieldsRel ks j a) (hb : FieldsRel ks j b) : a = b := by
  cases ha
  cases hb
  rfl

/-- Decimal place-value semantics; validation is a separate premise. -/
def decimal (bs : Bytes) : ℕ := bs.foldl (fun a b => 10 * a + (b.toNat - 48)) 0

def signedDecimal : Bytes → ℤ
  | 45 :: bs => -(decimal bs : ℤ)
  | bs => (decimal bs : ℤ)

inductive NatRel : JsonAST → ℕ → Prop where
  | intro (b : Bytes) (h : unsignedNumber b = true) : NatRel (.number b) (decimal b)

inductive IntRel : JsonAST → ℤ → Prop where
  | intro (b : Bytes) (h : canonicalNumber b = true) : IntRel (.number b) (signedDecimal b)

def natChecked : Checked NatRel
  | .number b => if h : unsignedNumber b = true then some ⟨decimal b, .intro b h⟩ else none
  | _ => none

def intChecked : Checked IntRel
  | .number b => if h : canonicalNumber b = true then
      some ⟨signedDecimal b, .intro b h⟩ else none
  | _ => none

theorem nat_unique {j : JsonAST} {a b : ℕ} (ha : NatRel j a) (hb : NatRel j b) : a = b := by
  cases ha
  cases hb
  rfl

theorem int_unique {j : JsonAST} {a b : ℤ} (ha : IntRel j a) (hb : IntRel j b) : a = b := by
  cases ha
  cases hb
  rfl

def identifierByte (b : UInt8) : Bool :=
  (65 ≤ b.toNat && b.toNat ≤ 90) || (97 ≤ b.toNat && b.toNat ≤ 122) || digit b || b == 95

def Identifier (b : Bytes) : Prop := b ≠ [] ∧ b.length ≤ 64 ∧ b.all identifierByte = true
instance (b : Bytes) : Decidable (Identifier b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

inductive IdentifierRel : JsonAST → Bytes → Prop where
  | intro (b : Bytes) (h : Identifier b) : IdentifierRel (.string b) b

def identifierChecked : Checked IdentifierRel
  | .string b => if h : Identifier b then some ⟨b, .intro b h⟩ else none
  | _ => none

theorem identifier_unique {j : JsonAST} {a b : Bytes}
    (ha : IdentifierRel j a) (hb : IdentifierRel j b) : a = b := by
  cases ha
  cases hb
  rfl

/-- A digest-shaped field is required, but neither digest correctness nor binding is checked. -/
def DigestShape (j : JsonAST) : Prop := ∃ b, j = .string b ∧ b.length = 64 ∧
  b.all (fun c => digit c || (97 ≤ c.toNat && c.toNat ≤ 102)) = true

def digestChecked : (j : JsonAST) → Option (PLift (DigestShape j))
  | .string b => if h : b.length = 64 ∧
        b.all (fun c => digit c || (97 ≤ c.toNat && c.toNat ≤ 102)) = true then
      some ⟨⟨b, rfl, h⟩⟩ else none
  | _ => none

/-- Positional list correspondence: no sorting, filtering or normalization. -/
inductive ItemsRel {α : Type} (r : JsonAST → α → Prop) : List JsonAST → List α → Prop where
  | nil : ItemsRel r [] []
  | cons {j : JsonAST} {a : α} {js : List JsonAST} {xs : List α}
      (head : r j a) (tail : ItemsRel r js xs) : ItemsRel r (j :: js) (a :: xs)

def itemsChecked {α : Type} {r : JsonAST → α → Prop} (d : Checked r) :
    (js : List JsonAST) → Option { xs : List α // ItemsRel r js xs }
  | [] => some ⟨[], .nil⟩
  | j :: js => do
      let a ← d j
      let xs ← itemsChecked d js
      pure ⟨a.val :: xs.val, .cons a.property xs.property⟩

theorem items_unique {α : Type} {r : JsonAST → α → Prop}
    (hr : ∀ (j : JsonAST) (a b : α), r j a → r j b → a = b)
    {js : List JsonAST} {a b : List α} (ha : ItemsRel r js a) (hb : ItemsRel r js b) : a = b := by
  induction ha generalizing b with
  | nil => cases hb; rfl
  | cons h t ih => cases hb with
    | cons h' t' => rw [hr _ _ _ h h', ih t']

theorem items_length {α : Type} {r : JsonAST → α → Prop} {js : List JsonAST} {xs : List α}
    (h : ItemsRel r js xs) : xs.length = js.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

inductive ArrayRel {α : Type} (r : JsonAST → α → Prop) : JsonAST → List α → Prop where
  | intro {js : List JsonAST} {xs : List α} (h : ItemsRel r js xs) : ArrayRel r (.array js) xs

def arrayChecked {α : Type} {r : JsonAST → α → Prop} (d : Checked r) : Checked (ArrayRel r)
  | .array js => do
      let xs ← itemsChecked d js
      pure ⟨xs.val, .intro xs.property⟩
  | _ => none

theorem array_unique {α : Type} {r : JsonAST → α → Prop}
    (hr : ∀ (j : JsonAST) (a b : α), r j a → r j b → a = b)
    {j : JsonAST} {a b : List α} (ha : ArrayRel r j a) (hb : ArrayRel r j b) : a = b := by
  cases ha with | intro ha => cases hb with | intro hb => exact items_unique hr ha hb

/-- Canonical rational terms and the frozen coefficient-size profile. -/
def GoodCoeff (num : ℤ) (den : ℕ) : Prop :=
  num ≠ 0 ∧ 0 < den ∧ Nat.gcd num.natAbs den = 1 ∧ num.natAbs < 2 ^ 256 ∧ den < 2 ^ 256
instance (num : ℤ) (den : ℕ) : Decidable (GoodCoeff num den) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

inductive CoeffRel : JsonAST → ℚ → Prop where
  | intro {jn jd : JsonAST} {num : ℤ} {den : ℕ}
      (hn : IntRel jn num) (hd : NatRel jd den) (hg : GoodCoeff num den) :
      CoeffRel (.array [jn, jd]) ((num : ℚ) / (den : ℚ))

def coeffChecked : Checked CoeffRel
  | .array [jn, jd] => do
      let num ← intChecked jn
      let den ← natChecked jd
      if h : GoodCoeff num.val den.val then
        pure ⟨(num.val : ℚ) / (den.val : ℚ), .intro num.property den.property h⟩
      else none
  | _ => none

theorem coeff_unique {j : JsonAST} {a b : ℚ}
    (ha : CoeffRel j a) (hb : CoeffRel j b) : a = b := by
  cases ha with
  | intro hn hd hg => cases hb with
    | intro hn' hd' hg' => rw [int_unique hn hn', nat_unique hd hd']

def GoodPowers (es : List ℕ) : Prop := (∀ e ∈ es, e ≤ 64) ∧ es.sum ≤ 128
instance (es : List ℕ) : Decidable (GoodPowers es) := inferInstanceAs (Decidable (_ ∧ _))

inductive TermRel (n : ℕ) : JsonAST → Term n → Prop where
  | intro {j jc je : JsonAST} {q : ℚ} {es : List ℕ}
      (hf : FieldsRel [bytes "coeff", bytes "powers"] j [jc, je])
      (hc : CoeffRel jc q) (he : ArrayRel NatRel je es)
      (hl : es.length = n) (hg : GoodPowers es) : TermRel n j (⟨es, hl⟩, q)

def termChecked (n : ℕ) (j : JsonAST) : Option { t : Term n // TermRel n j t } := do
  let fs ← fields [bytes "coeff", bytes "powers"] j
  match hf : fs.val with
  | [jc, je] => do
      let q ← coeffChecked jc
      let es ← arrayChecked natChecked je
      if hl : es.val.length = n then
        if hg : GoodPowers es.val then
          pure ⟨(⟨es.val, hl⟩, q.val),
            .intro (hf ▸ fs.property) q.property es.property hl hg⟩
        else none
      else none
  | _ => none

theorem term_unique {n : ℕ} {j : JsonAST} {a b : Term n}
    (ha : TermRel n j a) (hb : TermRel n j b) : a = b := by
  cases ha with
  | intro hf hc he hl hg => cases hb with
    | intro hf' hc' he' hl' hg' =>
      have h := fields_unique hf hf'
      simp only [List.cons.injEq, and_true] at h
      rcases h with ⟨rfl, rfl⟩
      have hq := coeff_unique hc hc'
      have hs := array_unique (fun j a b => @nat_unique j a b) he he'
      subst hs
      subst hq
      rfl

/-- Structural canonicality is checked, never repaired. -/
def PolyCanonical {n : ℕ} (p : SparsePoly n) : Prop :=
  p.Pairwise (fun a b => b.1 < a.1) ∧ (∀ t ∈ p, t.2 ≠ 0) ∧ p.length ≤ 256
instance {n : ℕ} (p : SparsePoly n) : Decidable (PolyCanonical p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

inductive PolyRel (n : ℕ) : JsonAST → SparsePoly n → Prop where
  | intro {j : JsonAST} {p : SparsePoly n}
      (terms : ArrayRel (TermRel n) j p) (canonical : PolyCanonical p) : PolyRel n j p

def polyChecked (n : ℕ) (j : JsonAST) : Option { p : SparsePoly n // PolyRel n j p } := do
  let p ← arrayChecked (termChecked n) j
  if h : PolyCanonical p.val then pure ⟨p.val, .intro p.property h⟩ else none

/-- Public partial polynomial decoder, preserving every accepted input term. -/
def decodePoly (n : ℕ) (j : JsonAST) : Option (SparsePoly n) := (polyChecked n j).map Subtype.val

theorem decodePoly_sound {n : ℕ} {j : JsonAST} {p : SparsePoly n}
    (h : decodePoly n j = some p) : PolyRel n j p := by
  unfold decodePoly at h
  cases he : polyChecked n j with
  | none => simp [he] at h
  | some a =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst p
    exact a.property

theorem poly_unique {n : ℕ} {j : JsonAST} {a b : SparsePoly n}
    (ha : PolyRel n j a) (hb : PolyRel n j b) : a = b := by
  cases ha with
  | intro ha _ => cases hb with
    | intro hb _ => exact array_unique (fun j a b => @term_unique _ j a b) ha hb

theorem decodePoly_canonical {n : ℕ} {j : JsonAST} {p : SparsePoly n}
    (h : decodePoly n j = some p) : PolyCanonical p := by
  cases decodePoly_sound h with | intro _ hc => exact hc

theorem decodePoly_preserves_terms {n : ℕ} {js : List JsonAST} {p : SparsePoly n}
    (h : decodePoly n (.array js) = some p) : ItemsRel (TermRel n) js p := by
  cases decodePoly_sound h with | intro ht _ => cases ht with | intro hs => exact hs

inductive WrappedPolyRel (n : ℕ) : JsonAST → SparsePoly n → Prop where
  | intro {j node : JsonAST} {p : SparsePoly n}
      (hf : FieldsRel [bytes "poly"] j [node]) (hp : PolyRel n node p) : WrappedPolyRel n j p

def wrappedPolyChecked (n : ℕ) (j : JsonAST) :
    Option { p : SparsePoly n // WrappedPolyRel n j p } := do
  let fs ← fields [bytes "poly"] j
  match hf : fs.val with
  | [node] => do
      let p ← polyChecked n node
      pure ⟨p.val, .intro (hf ▸ fs.property) p.property⟩
  | _ => none

theorem wrappedPoly_unique {n : ℕ} {j : JsonAST} {a b : SparsePoly n}
    (ha : WrappedPolyRel n j a) (hb : WrappedPolyRel n j b) : a = b := by
  cases ha with
  | intro hf hp => cases hb with
    | intro hf' hp' =>
      have h := fields_unique hf hf'
      simp only [List.cons.injEq, and_true] at h
      subst h
      exact poly_unique hp hp'

inductive EntryRel (n : ℕ) (key : Bytes) : JsonAST → (Bytes × SparsePoly n) → Prop where
  | intro {j ji jp : JsonAST} {id : Bytes} {p : SparsePoly n}
      (hf : FieldsRel [key, bytes "poly"] j [ji, jp])
      (hi : IdentifierRel ji id) (hp : PolyRel n jp p) : EntryRel n key j (id, p)

def entryChecked (n : ℕ) (key : Bytes) (j : JsonAST) :
    Option { e : Bytes × SparsePoly n // EntryRel n key j e } := do
  let fs ← fields [key, bytes "poly"] j
  match hf : fs.val with
  | [ji, jp] => do
      let id ← identifierChecked ji
      let p ← polyChecked n jp
      pure ⟨(id.val, p.val), .intro (hf ▸ fs.property) id.property p.property⟩
  | _ => none

theorem entry_unique {n : ℕ} {key : Bytes} {j : JsonAST} {a b : Bytes × SparsePoly n}
    (ha : EntryRel n key j a) (hb : EntryRel n key j b) : a = b := by
  cases ha with
  | intro hf hi hp => cases hb with
    | intro hf' hi' hp' =>
      have h := fields_unique hf hf'
      simp only [List.cons.injEq, and_true] at h
      rcases h with ⟨rfl, rfl⟩
      rw [identifier_unique hi hi', poly_unique hp hp']

inductive LiteralRel (b : Bytes) : JsonAST → Prop where
  | intro : LiteralRel b (.string b)

def literalChecked (b : Bytes) : (j : JsonAST) → Option (PLift (LiteralRel b j))
  | .string s => if h : s = b then some ⟨h ▸ LiteralRel.intro⟩ else none
  | _ => none

def passportKeys : List Bytes :=
  [bytes "format_version", bytes "hypotheses", bytes "problem_id", bytes "profile_id",
   bytes "target", bytes "variables"]
def certificateKeys : List Bytes :=
  [bytes "format_version", bytes "multipliers", bytes "problem_id", bytes "profile_id"]

/-- An explicitly unbound task. It does not retain or certify a hash binding. -/
abbrev UnboundTask := Σ n : ℕ, Σ m : ℕ, Passport n m × Certificate n m

def pack (vs : List Bytes) (hs : List (Bytes × SparsePoly vs.length))
    (target : SparsePoly vs.length) (qs : List (Bytes × SparsePoly vs.length))
    (hlen : qs.length = hs.length) : UnboundTask :=
  ⟨vs.length, hs.length,
    { hypotheses := fun i => (hs.get i).2, target := target },
    { multipliers := fun i => (qs.get ⟨i.val, by omega⟩).2 }⟩

/-- Declarative schema contract. Constructors mention no decoding algorithm.
`problem_id` fields are syntax-checked but are deliberately not compared or hashed. -/
inductive SchemaDecodeRel (jp jc : JsonAST) : UnboundTask → Prop where
  | intro {vf hj pid prof tj vj cf qj cid cprof : JsonAST}
      {vs : List Bytes} {hs qs : List (Bytes × SparsePoly vs.length)}
      {target : SparsePoly vs.length}
      (hpc : IsCanonicalAST jp) (hcc : IsCanonicalAST jc)
      (hpf : FieldsRel passportKeys jp [vf, hj, pid, prof, tj, vj])
      (hcf : FieldsRel certificateKeys jc [cf, qj, cid, cprof])
      (hvf : LiteralRel (bytes "1.0") vf) (hcfv : LiteralRel (bytes "1.0") cf)
      (hprof : LiteralRel (bytes "ALCC-JSON-1") prof)
      (hcprof : LiteralRel (bytes "ALCC-JSON-1") cprof)
      (hpid : DigestShape pid) (hcid : DigestShape cid)
      (hvs : ArrayRel IdentifierRel vj vs)
      (hhs : ArrayRel (EntryRel vs.length (bytes "id")) hj hs)
      (ht : WrappedPolyRel vs.length tj target)
      (hqs : ArrayRel (EntryRel vs.length (bytes "hypothesis_id")) qj qs)
      (hvu : vs.Nodup) (hhu : (hs.map Prod.fst).Nodup)
      (hvn : vs.length ≤ 16) (hhn : hs.length ≤ 32)
      (halign : qs.map Prod.fst = hs.map Prod.fst)
      (hlen : qs.length = hs.length) :
      SchemaDecodeRel jp jc (pack vs hs target qs hlen)

def schemaChecked (jp jc : JsonAST) : Option { t : UnboundTask // SchemaDecodeRel jp jc t } := do
  if hpc : IsCanonicalAST jp then
    if hcc : IsCanonicalAST jc then
      let pf ← fields passportKeys jp
      let cf ← fields certificateKeys jc
      match hpf : pf.val, hcf : cf.val with
      | [vf, hj, pid, prof, tj, vj], [cvf, qj, cid, cprof] => do
          let hvf ← literalChecked (bytes "1.0") vf
          let hcfv ← literalChecked (bytes "1.0") cvf
          let hprof ← literalChecked (bytes "ALCC-JSON-1") prof
          let hcprof ← literalChecked (bytes "ALCC-JSON-1") cprof
          let hpid ← digestChecked pid
          let hcid ← digestChecked cid
          let vs ← arrayChecked identifierChecked vj
          if hvu : vs.val.Nodup then
            if hvn : vs.val.length ≤ 16 then
              let hs ← arrayChecked (entryChecked vs.val.length (bytes "id")) hj
              let target ← wrappedPolyChecked vs.val.length tj
              let qs ← arrayChecked (entryChecked vs.val.length (bytes "hypothesis_id")) qj
              if hhu : (hs.val.map Prod.fst).Nodup then
                if hhn : hs.val.length ≤ 32 then
                  if ha : qs.val.map Prod.fst = hs.val.map Prod.fst then
                    have hl : qs.val.length = hs.val.length := by
                      simpa using congrArg List.length ha
                    pure ⟨pack vs.val hs.val target.val qs.val hl,
                      .intro hpc hcc (hpf ▸ pf.property) (hcf ▸ cf.property)
                        hvf.down hcfv.down hprof.down hcprof.down hpid.down hcid.down
                        vs.property hs.property target.property qs.property hvu hhu hvn hhn ha hl⟩
                  else none
                else none
              else none
            else none
          else none
      | _, _ => none
    else none
  else none

/-- Returns only schema-validated structures, never an admission or identity verdict. -/
def decodeSchema (jp jc : JsonAST) : Option UnboundTask := (schemaChecked jp jc).map Subtype.val

theorem decodeSchema_sound {jp jc : JsonAST} {t : UnboundTask}
    (h : decodeSchema jp jc = some t) : SchemaDecodeRel jp jc t := by
  unfold decodeSchema at h
  cases he : schemaChecked jp jc with
  | none => simp [he] at h
  | some a =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst t
    exact a.property

theorem schemaDecodeRel_deterministic {jp jc : JsonAST} {a b : UnboundTask}
    (ha : SchemaDecodeRel jp jc a) (hb : SchemaDecodeRel jp jc b) : a = b := by
  cases ha with
  | intro hpc hcc hpf hcf hvf hcfv hprof hcprof hpid hcid hvs hhs ht hqs
      hvu hhu hvn hhn halign hlen =>
    cases hb with
    | intro hpc' hcc' hpf' hcf' hvf' hcfv' hprof' hcprof' hpid' hcid' hvs' hhs' ht' hqs'
        hvu' hhu' hvn' hhn' halign' hlen' =>
      have hp := fields_unique hpf hpf'
      have hc := fields_unique hcf hcf'
      simp only [List.cons.injEq, and_true] at hp hc
      rcases hp with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      rcases hc with ⟨rfl, rfl, rfl, rfl⟩
      have hv := array_unique (fun j a b => @identifier_unique j a b) hvs hvs'
      subst hv
      have hh := array_unique (fun j a b => @entry_unique _ _ j a b) hhs hhs'
      have hq := array_unique (fun j a b => @entry_unique _ _ j a b) hqs hqs'
      have htgt := wrappedPoly_unique ht ht'
      subst hh
      subst hq
      subst htgt
      rfl

/-- Position-by-position preservation, including empty lists. -/
theorem items_at {α : Type} {r : JsonAST → α → Prop} {js : List JsonAST} {xs : List α}
    (h : ItemsRel r js xs) (i : ℕ) (hj : i < js.length) (hx : i < xs.length) :
    r js[i] xs[i] := by
  induction h generalizing i with
  | nil => simp at hj
  | cons head tail ih =>
    cases i with
    | zero => simpa using head
    | succ i => exact ih i (by simpa using hj) (by simpa using hx)

theorem decodePoly_at {n : ℕ} {js : List JsonAST} {p : SparsePoly n}
    (h : decodePoly n (.array js) = some p) (i : ℕ)
    (hj : i < js.length) (hp : i < p.length) : TermRel n js[i] p[i] :=
  items_at (decodePoly_preserves_terms h) i hj hp

theorem decodePoly_length {n : ℕ} {js : List JsonAST} {p : SparsePoly n}
    (h : decodePoly n (.array js) = some p) : p.length = js.length :=
  items_length (decodePoly_preserves_terms h)

theorem decodePoly_no_duplicates {n : ℕ} {j : JsonAST} {p : SparsePoly n}
    (h : decodePoly n j = some p) : (p.map Prod.fst).Nodup := by
  change (p.map Prod.fst).Pairwise (fun a b => a ≠ b)
  rw [List.pairwise_map]
  exact (decodePoly_canonical h).1.imp (fun hlt => ne_of_gt hlt)

/-- Coefficients and exponent vectors are interpreted exactly, not normalized. -/
theorem term_exact {n : ℕ} {j : JsonAST} {t : Term n} (h : TermRel n j t) :
    ∃ (jc je jn jd : JsonAST) (num : ℤ) (den : ℕ),
      FieldsRel [bytes "coeff", bytes "powers"] j [jc, je] ∧
      jc = .array [jn, jd] ∧ IntRel jn num ∧ NatRel jd den ∧ GoodCoeff num den ∧
      ArrayRel NatRel je t.1.val ∧ t.2 = (num : ℚ) / (den : ℚ) := by
  cases h with
  | intro hf hc he hl hg =>
    cases hc with
    | intro hn hd hgood => exact ⟨_, _, _, _, _, _, hf, rfl, hn, hd, hgood, he, rfl⟩

/-- The same AST pair cannot produce two distinct dependent task values. -/
theorem decodeSchema_unique {jp jc : JsonAST} {a b : UnboundTask}
    (ha : decodeSchema jp jc = some a) (hb : decodeSchema jp jc = some b) : a = b :=
  schemaDecodeRel_deterministic (decodeSchema_sound ha) (decodeSchema_sound hb)

end AlgebraicCertificateSchema
