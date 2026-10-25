/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.List.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! # ALCC-SYNTAX-1: isolated canonical ASCII syntax.
No ALCC schema, SHA-256, Python refinement or operational admission is asserted.
-/
namespace AlgebraicCertificateSyntax

abbrev Bytes := List UInt8

def hex (n : Nat) : UInt8 := UInt8.ofNat (if n < 10 then 48 + n else 87 + n)

def escapeByte (b : UInt8) : Bytes :=
  if b = 34 then [92, 34]
  else if b = 92 then [92, 92]
  else if b = 8 then [92, 98]
  else if b = 12 then [92, 102]
  else if b = 10 then [92, 110]
  else if b = 13 then [92, 114]
  else if b = 9 then [92, 116]
  else if b.toNat < 32 ∨ b = 127 then [92, 117, 48, 48, hex (b.toNat / 16), hex (b.toNat % 16)]
  else [b]

def serializeString (s : Bytes) : Bytes := 34 :: s.flatMap escapeByte ++ [34]

def unhex (b : UInt8) : Option Nat :=
  if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b.toNat ∧ b.toNat ≤ 102 then some (b.toNat - 87)
  else none

def readEscape : Bytes → Option (UInt8 × Bytes)
  | 34 :: rest => some (34, rest)
  | 92 :: rest => some (92, rest)
  | 98 :: rest => some (8, rest)
  | 102 :: rest => some (12, rest)
  | 110 :: rest => some (10, rest)
  | 114 :: rest => some (13, rest)
  | 116 :: rest => some (9, rest)
  | 117 :: 48 :: 48 :: a :: b :: rest => do
      let x ← unhex a
      let y ← unhex b
      return (UInt8.ofNat (16 * x + y), rest)
  | _ => none

def readString : Nat → Bytes → Option (Bytes × Bytes)
  | 0, _ => none
  | fuel + 1, b :: rest =>
      if b = 34 then some ([], rest)
      else if b = 92 then do
        let (c, tail) ← readEscape rest
        let (s, tail') ← readString fuel tail
        return (c :: s, tail')
      else do
        let (s, tail) ← readString fuel rest
        return (b :: s, tail)
  | _ + 1, [] => none

def Ascii (s : Bytes) : Prop := ∀ b ∈ s, b.toNat < 128

-- A finite table proof, with arbitrary continuation bytes.
theorem readString_byte (b : UInt8) (s : Bytes) (fuel : Nat)
    (hb : b.toNat < 128) :
    readString (fuel + 1) (escapeByte b ++ s) =
      (do let (v, r) ← readString fuel s; return (b :: v, r)) := by
  have hbound := b.toNat_lt
  generalize hn : b.toNat = n at *
  have beq : b = UInt8.ofNat n := by simp [← hn]
  subst b
  interval_cases n <;> simp [escapeByte, hex, readString, readEscape, unhex]

theorem readString_encode (s tail : Bytes) (fuel : Nat) (ha : Ascii s)
    (hf : s.length < fuel) :
    readString fuel (s.flatMap escapeByte ++ 34 :: tail) = some (s, tail) := by
  induction s generalizing fuel with
  | nil => cases fuel <;> simp_all [readString]
  | cons b s ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp only [List.flatMap_cons, List.append_assoc]
      rw [readString_byte b _ fuel (ha b (by simp))]
      rw [ih fuel (fun c hc => ha c (by simp [hc])) (by simpa using hf)]
      rfl


inductive JsonAST where
  | string : Bytes → JsonAST
  | number : Bytes → JsonAST
  | null : JsonAST
  | boolean : Bool → JsonAST
  | array : List JsonAST → JsonAST
  | object : List (Bytes × JsonAST) → JsonAST
  deriving Repr

def digit (b : UInt8) : Bool := 48 ≤ b.toNat && b.toNat ≤ 57

def numberChar (b : UInt8) : Bool := digit b || b == 45

def unsignedNumber : Bytes → Bool
  | [48] => true
  | b :: bs => (49 ≤ b.toNat && b.toNat ≤ 57) && bs.all digit
  | [] => false

def canonicalNumber : Bytes → Bool
  | 45 :: bs => unsignedNumber bs && bs != [48]
  | bs => unsignedNumber bs

mutual
  def serializeCanonical : JsonAST → Bytes
    | .string s => serializeString s
    | .number s => s
    | .null => [110, 117, 108, 108]
    | .boolean true => [116, 114, 117, 101]
    | .boolean false => [102, 97, 108, 115, 101]
    | .array xs => 91 :: arrayBytes xs
    | .object xs => 123 :: objectBytes xs
  def arrayBytes : List JsonAST → Bytes
    | [] => [93]
    | x :: xs => serializeCanonical x ++ (if xs.isEmpty then [93] else 44 :: arrayBytes xs)
  def objectBytes : List (Bytes × JsonAST) → Bytes
    | [] => [125]
    | (k, v) :: xs => serializeString k ++ 58 :: serializeCanonical v ++
        (if xs.isEmpty then [125] else 44 :: objectBytes xs)
end

mutual
  def canonicalAST : JsonAST → Bool
    | .string s => s.all (fun b => b.toNat < 128)
    | .number s => canonicalNumber s
    | .null | .boolean _ => true
    | .array xs => canonicalArray xs
    | .object xs => canonicalObject xs
  def canonicalArray : List JsonAST → Bool
    | [] => true
    | x :: xs => canonicalAST x && canonicalArray xs
  def canonicalObject : List (Bytes × JsonAST) → Bool
    | [] => true
    | (k,v) :: xs => k.all (fun b => b.toNat < 128) && canonicalAST v &&
        canonicalObject xs && (match xs with | [] => true | (k',_) :: _ => decide (k < k'))
end

abbrev IsCanonicalAST (t : JsonAST) : Prop := canonicalAST t = true

def NumberBoundary (bs : Bytes) : Prop := ∀ b, bs.head? = some b → numberChar b = false

mutual
  def parseValue : Nat → Bytes → Option (JsonAST × Bytes)
    | 0, _ => none
    | fuel + 1, bs =>
      if bs.takeWhile numberChar != [] then
        some (.number (bs.takeWhile numberChar), bs.dropWhile numberChar)
      else match bs with
      | 34 :: tail => do
          let (s, rest) ← readString (fuel + 1) tail
          return (.string s, rest)
      | 91 :: tail => do
          let (xs, rest) ← parseArray fuel tail
          return (.array xs, rest)
      | 123 :: tail => do
          let (xs, rest) ← parseObject fuel tail
          return (.object xs, rest)
      | 110 :: 117 :: 108 :: 108 :: rest => some (.null, rest)
      | 116 :: 114 :: 117 :: 101 :: rest => some (.boolean true, rest)
      | 102 :: 97 :: 108 :: 115 :: 101 :: rest => some (.boolean false, rest)
      | _ => none
  def parseArray : Nat → Bytes → Option (List JsonAST × Bytes)
    | 0, _ => none
    | fuel + 1, bs => match parseValue fuel bs with
      | none => match bs with | 93 :: tail => some ([], tail) | _ => none
      | some (v, rest) => match rest with
        | 93 :: tail => some ([v], tail)
        | 44 :: tail => do
            let (vs, tail') ← parseArray fuel tail
            return (v :: vs, tail')
        | _ => none
  def parseObject : Nat → Bytes → Option (List (Bytes × JsonAST) × Bytes)
    | 0, _ => none
    | _ + 1, 125 :: tail => some ([], tail)
    | fuel + 1, 34 :: keyBytes => do
        let (k, 58 :: valueBytes) ← readString fuel keyBytes | none
        let (v, rest) ← parseValue fuel valueBytes
        match rest with
        | 125 :: tail => return ([(k, v)], tail)
        | 44 :: tail => do
            let (vs, tail') ← parseObject fuel tail
            return ((k, v) :: vs, tail')
        | _ => none
    | _ + 1, _ => none

end


theorem escapeByte_length (b : UInt8) : 0 < (escapeByte b).length := by
  simp only [escapeByte]
  split_ifs <;> simp

theorem escaped_length (s : Bytes) : s.length ≤ (s.flatMap escapeByte).length := by
  induction s with
  | nil => simp
  | cons b s ih =>
    have hb := escapeByte_length b
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem unsigned_number_chars (s : Bytes) (h : unsignedNumber s = true) :
    s ≠ [] ∧ ∀ b ∈ s, numberChar b = true := by
  unfold unsignedNumber at h
  split at h
  · simp [numberChar, digit]
  · rename_i b bs _
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    constructor
    · simp
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp [numberChar, digit, Nat.le_trans (by decide : 48 ≤ 49) h.1.1, h.1.2]
      · simp [numberChar, h.2 c hc]
  · contradiction

theorem canonical_number_chars (s : Bytes) (h : canonicalNumber s = true) :
    s ≠ [] ∧ ∀ b ∈ s, numberChar b = true := by
  unfold canonicalNumber at h
  split at h
  · rename_i bs
    simp only [Bool.and_eq_true] at h
    have hu := unsigned_number_chars bs h.1
    constructor
    · simp
    · intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · decide
      · exact hu.2 b hb
  · exact unsigned_number_chars _ h

theorem read_number_append (s tail : Bytes) (hs : ∀ b ∈ s, numberChar b = true)
    (ht : NumberBoundary tail) :
    (s ++ tail).takeWhile numberChar = s ∧ (s ++ tail).dropWhile numberChar = tail := by
  have ht1 : tail.takeWhile numberChar = [] := by
    cases tail with
    | nil => rfl
    | cons b bs => simp [ht b rfl]
  have ht2 : tail.dropWhile numberChar = tail := by
    cases tail with
    | nil => rfl
    | cons b bs => simp [ht b rfl]
  simp [List.takeWhile_append_of_pos hs, List.dropWhile_append_of_pos hs, ht1, ht2]

def ValueRoundTrip (t : JsonAST) : Prop := ∀ fuel tail,
  IsCanonicalAST t → (serializeCanonical t).length < fuel → NumberBoundary tail →
  parseValue fuel (serializeCanonical t ++ tail) = some (t, tail)

def ArrayRoundTrip (xs : List JsonAST) : Prop := ∀ fuel tail,
  canonicalArray xs = true → (arrayBytes xs).length < fuel →
  parseArray fuel (arrayBytes xs ++ tail) = some (xs, tail)

def ObjectRoundTrip (xs : List (Bytes × JsonAST)) : Prop := ∀ fuel tail,
  canonicalObject xs = true → (objectBytes xs).length < fuel →
  parseObject fuel (objectBytes xs ++ tail) = some (xs, tail)


theorem value_roundTrip (t : JsonAST) : ValueRoundTrip t := by
  apply JsonAST.rec (motive_1 := ValueRoundTrip) (motive_2 := ArrayRoundTrip)
    (motive_3 := ObjectRoundTrip) (motive_4 := fun kv => ValueRoundTrip kv.2)
  · intro s fuel tail ha hf _
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hs : Ascii s := by simpa [IsCanonicalAST, canonicalAST, Ascii] using ha
      have hl := escaped_length s
      have hb : s.length < fuel + 1 := by
        simp only [serializeCanonical, serializeString, List.length_cons, List.length_append] at hf
        omega
      simp [serializeCanonical, serializeString, parseValue, numberChar, digit,
        List.append_assoc, readString_encode s tail (fuel + 1) hs hb]
  · intro s fuel tail ha hf ht
    have hn := canonical_number_chars s ha
    have hp := read_number_append s tail hn.2 ht
    cases fuel with
    | zero => omega
    | succ fuel => simp [serializeCanonical, parseValue, hp.1, hp.2, hn.1]
  · intro fuel tail _ hf _
    cases fuel with
    | zero => omega
    | succ fuel => simp [serializeCanonical, parseValue, numberChar, digit]
  · intro b fuel tail _ hf _
    cases fuel with
    | zero => omega
    | succ fuel => cases b <;> simp [serializeCanonical, parseValue, numberChar, digit]
  · intro xs ih fuel tail ha hf _
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hh : (arrayBytes xs).length < fuel := by simpa [serializeCanonical] using hf
      simp [serializeCanonical, parseValue, numberChar, digit, ih fuel tail ha hh]
  · intro xs ih fuel tail ha hf _
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hh : (objectBytes xs).length < fuel := by simpa [serializeCanonical] using hf
      simp [serializeCanonical, parseValue, numberChar, digit, ih fuel tail ha hh]
  · intro fuel tail _ hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases fuel <;> simp [arrayBytes, parseArray, parseValue, numberChar, digit]
  · intro x xs ihx ihxs fuel tail ha hf
    have hc := Bool.and_eq_true_iff.mp ha
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases xs with
      | nil =>
        have hx : (serializeCanonical x).length < fuel := by simpa [arrayBytes] using hf
        have hparse := ihx fuel (93 :: tail) hc.1 hx (by simp [NumberBoundary, numberChar, digit])
        simp [arrayBytes, List.append_assoc, parseArray, hparse]
      | cons y ys =>
        have hx : (serializeCanonical x).length < fuel := by
          simp only [arrayBytes, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
            List.length_append, List.length_cons] at hf
          omega
        have ht : (arrayBytes (y :: ys)).length < fuel := by
          simp only [arrayBytes, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
            List.length_append, List.length_cons] at hf ⊢
          omega
        have hparse := ihx fuel (44 :: arrayBytes (y :: ys) ++ tail) hc.1 hx
          (by simp [NumberBoundary, numberChar, digit])
        have htail := ihxs fuel tail hc.2 ht
        change parseArray (fuel + 1)
          ((serializeCanonical x ++ 44 :: arrayBytes (y :: ys)) ++ tail) = _
        rw [List.append_assoc]
        unfold parseArray
        rw [hparse]
        simp only [List.cons_append, htail]
        rfl
  · intro fuel tail _ hf
    cases fuel with
    | zero => omega
    | succ fuel => simp [objectBytes, parseObject]
  · intro kv xs ihkv ihxs fuel tail ha hf
    rcases kv with ⟨k,v⟩
    have hh := ha
    simp only [canonicalObject, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hh
    have hc : Ascii k ∧ IsCanonicalAST v ∧ canonicalObject xs = true :=
      ⟨hh.1.1.1, hh.1.1.2, hh.1.2⟩
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hk := escaped_length k
      simp only [List.length_flatMap] at hk
      cases xs with
      | nil =>
        have hv : (serializeCanonical v).length < fuel := by
          simp [objectBytes, serializeString] at hf
          omega
        have hkey : k.length < fuel := by
          simp [objectBytes, serializeString] at hf
          omega
        have hparse := ihkv fuel (125 :: tail) hc.2.1 hv
          (by simp [NumberBoundary, numberChar, digit])
        rw [objectBytes]
        simp only [List.isEmpty_nil, if_true,
          serializeString, List.append_assoc, List.cons_append, List.nil_append]
        change parseObject (fuel + 1)
          (34 :: (k.flatMap escapeByte ++ 34 :: 58 :: (serializeCanonical v ++ 125 :: tail))) = _
        rw [parseObject, readString_encode k (58 :: (serializeCanonical v ++ 125 :: tail))
          fuel hc.1 hkey]
        simp [hparse, Bind.bind, Option.bind, Pure.pure]
      | cons q qs =>
        have hv : (serializeCanonical v).length < fuel := by
          simp [objectBytes, serializeString] at hf
          omega
        have hkey : k.length < fuel := by
          simp [objectBytes, serializeString] at hf
          omega
        have ht : (objectBytes (q :: qs)).length < fuel := by
          simp only [objectBytes, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
            List.length_append, List.length_cons] at hf ⊢
          omega
        have hparse := ihkv fuel (44 :: objectBytes (q :: qs) ++ tail) hc.2.1 hv
          (by simp [NumberBoundary, numberChar, digit])
        have htail := ihxs fuel tail hc.2.2 ht
        rw [objectBytes]
        simp only [List.isEmpty_cons,
          serializeString, List.append_assoc, List.cons_append, List.nil_append]
        change parseObject (fuel + 1)
          (34 :: (k.flatMap escapeByte ++ 34 :: 58 ::
            (serializeCanonical v ++ 44 :: (objectBytes (q :: qs) ++ tail)))) = _
        rw [parseObject, readString_encode k
          (58 :: (serializeCanonical v ++ 44 :: (objectBytes (q :: qs) ++ tail))) fuel hc.1 hkey]
        simp only [List.cons_append] at hparse
        simp [hparse, htail, Bind.bind, Option.bind, Pure.pure]
  · intro k v ih
    exact ih


/- A generative grammar for canonical ASCII token spellings. It does not call the parser.
Object ordering and duplicate rejection are separate structural conditions. -/
mutual
  inductive ParseRel : Bytes → JsonAST → Prop where
    | string (s : Bytes) (ha : Ascii s) :
        ParseRel (34 :: s.flatMap escapeByte ++ [34]) (.string s)
    | number (s : Bytes) (hn : canonicalNumber s = true) : ParseRel s (.number s)
    | null : ParseRel [110,117,108,108] .null
    | boolTrue : ParseRel [116,114,117,101] (.boolean true)
    | boolFalse : ParseRel [102,97,108,115,101] (.boolean false)
    | array {bs : Bytes} {xs : List JsonAST} (h : ArrayRel bs xs) : ParseRel (91 :: bs) (.array xs)
    | object {bs : Bytes} {xs : List (Bytes × JsonAST)} (h : ObjectRel bs xs) :
        ParseRel (123 :: bs) (.object xs)
  inductive ArrayRel : Bytes → List JsonAST → Prop where
    | nil : ArrayRel [93] []
    | one {b : Bytes} {x : JsonAST} (h : ParseRel b x) : ArrayRel (b ++ [93]) [x]
    | cons {b bs : Bytes} {x y : JsonAST} {ys : List JsonAST}
        (h : ParseRel b x) (hs : ArrayRel bs (y :: ys)) :
        ArrayRel (b ++ 44 :: bs) (x :: y :: ys)
  inductive ObjectRel : Bytes → List (Bytes × JsonAST) → Prop where
    | nil : ObjectRel [125] []
    | one {k b : Bytes} {v : JsonAST} (hk : Ascii k) (hv : ParseRel b v) :
        ObjectRel ((34 :: k.flatMap escapeByte ++ [34]) ++ 58 :: b ++ [125]) [(k,v)]
    | cons {k b bs : Bytes} {v : JsonAST} {q : Bytes × JsonAST} {qs : List (Bytes × JsonAST)}
        (hk : Ascii k) (hv : ParseRel b v) (hs : ObjectRel bs (q :: qs)) :
        ObjectRel ((34 :: k.flatMap escapeByte ++ [34]) ++ 58 :: b ++ 44 :: bs)
          ((k,v) :: q :: qs)
end

/-- The grammar derives the serialization independently of the decoding algorithm. -/
theorem serialize_grammar (t : JsonAST) (ht : IsCanonicalAST t) :
    ParseRel (serializeCanonical t) t := by
  apply JsonAST.rec
    (motive_1 := fun t => IsCanonicalAST t → ParseRel (serializeCanonical t) t)
    (motive_2 := fun xs => canonicalArray xs = true → ArrayRel (arrayBytes xs) xs)
    (motive_3 := fun xs => canonicalObject xs = true → ObjectRel (objectBytes xs) xs)
    (motive_4 := fun kv => IsCanonicalAST kv.2 →
      ParseRel (serializeCanonical kv.2) kv.2) _ _ _ _ _ _ _ _ _ _ _ t ht
  · intro s ha
    exact ParseRel.string s (by simpa [IsCanonicalAST, canonicalAST, Ascii] using ha)
  · intro s hn
    exact ParseRel.number s hn
  · intro _
    exact ParseRel.null
  · intro b _
    cases b
    · exact ParseRel.boolFalse
    · exact ParseRel.boolTrue
  · intro xs ih ha
    exact ParseRel.array (ih ha)
  · intro xs ih ha
    exact ParseRel.object (ih ha)
  · intro _
    exact ArrayRel.nil
  · intro x xs hx hxs ha
    have h := Bool.and_eq_true_iff.mp ha
    cases xs with
    | nil => exact ArrayRel.one (hx h.1)
    | cons y ys => exact ArrayRel.cons (hx h.1) (hxs h.2)
  · intro _
    exact ObjectRel.nil
  · intro kv xs hv hxs ha
    rcases kv with ⟨k,v⟩
    simp only [canonicalObject, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ha
    cases xs with
    | nil => exact ObjectRel.one ha.1.1.1 (hv ha.1.1.2)
    | cons q qs => exact ObjectRel.cons ha.1.1.1 (hv ha.1.1.2) (hxs ha.1.2)
  · intro k v ih
    exact ih

/-- Canonical serialization is injective on canonical trees, without resource assumptions. -/
theorem serialize_injective {a b : JsonAST} (ha : IsCanonicalAST a)
    (hb : IsCanonicalAST b) (h : serializeCanonical a = serializeCanonical b) : a = b := by
  have pa := value_roundTrip a ((serializeCanonical a).length + 1) [] ha (by omega)
    (by simp [NumberBoundary])
  have pb := value_roundTrip b ((serializeCanonical a).length + 1) [] hb (by rw [← h]; omega)
    (by simp [NumberBoundary])
  simp only [List.append_nil] at pa pb
  rw [← h, pa] at pb
  exact congrArg Prod.fst (Option.some.inj pb)

structure CanonicalParseRel (b : Bytes) (t : JsonAST) : Prop where
  grammar : ParseRel b t
  canonical : IsCanonicalAST t
  bytes : b = serializeCanonical t

mutual
  def treeDepth : JsonAST → Nat
    | .array xs => 1 + arrayDepth xs
    | .object xs => 1 + objectDepth xs
    | _ => 0
  def arrayDepth : List JsonAST → Nat
    | [] => 0
    | x :: xs => max (treeDepth x) (arrayDepth xs)
  def objectDepth : List (Bytes × JsonAST) → Nat
    | [] => 0
    | (_,v) :: xs => max (treeDepth v) (objectDepth xs)
end

mutual
  def nodeCount : JsonAST → Nat
    | .array xs => 1 + arrayNodes xs
    | .object xs => 1 + objectNodes xs
    | _ => 1
  def arrayNodes : List JsonAST → Nat
    | [] => 0
    | x :: xs => nodeCount x + arrayNodes xs
  def objectNodes : List (Bytes × JsonAST) → Nat
    | [] => 0
    | (_,v) :: xs => 1 + nodeCount v + objectNodes xs
end

def maxDepth : Nat := 16
def maxBytes : Nat := 1048576
def maxNodes : Nat := 1048576

def WithinResourceLimits (t : JsonAST) : Prop :=
  treeDepth t ≤ maxDepth ∧ (serializeCanonical t).length ≤ maxBytes ∧ nodeCount t ≤ maxNodes

instance (t : JsonAST) : Decidable (WithinResourceLimits t) := inferInstanceAs
  (Decidable (_ ∧ _ ∧ _))

/-- Byte-length fuel guarantees termination. The bounds describe admitted trees, not OS memory. -/
def parseCanonical (bs : Bytes) : Option JsonAST :=
  if bs.length ≤ maxBytes then do
    let (t, rest) ← parseValue (bs.length + 1) bs
    if rest = [] ∧ IsCanonicalAST t ∧ WithinResourceLimits t ∧ bs = serializeCanonical t
    then some t else none
  else none

theorem parseCanonical_sound {bs : Bytes} {t : JsonAST}
    (h : parseCanonical bs = some t) : CanonicalParseRel bs t := by
  unfold parseCanonical at h
  split at h
  · cases hp : parseValue (bs.length + 1) bs with
    | none => simp [hp] at h
    | some pair =>
      rcases pair with ⟨v, rest⟩
      simp only [hp] at h
      dsimp only [Bind.bind, Option.bind] at h
      split at h
      · rename_i hc
        have heq : v = t := by simpa using h
        subst v
        exact ⟨hc.2.2.2 ▸ serialize_grammar t hc.2.1, hc.2.1, hc.2.2.2⟩
      · contradiction
  · contradiction

theorem canonicalParse_deterministic {bs : Bytes} {a b : JsonAST}
    (ha : CanonicalParseRel bs a) (hb : CanonicalParseRel bs b) : a = b :=
  serialize_injective ha.canonical hb.canonical (ha.bytes.symm.trans hb.bytes)

theorem parseCanonical_complete (t : JsonAST) (hc : IsCanonicalAST t)
    (hr : WithinResourceLimits t) : parseCanonical (serializeCanonical t) = some t := by
  have hp := value_roundTrip t ((serializeCanonical t).length + 1) [] hc (by omega)
    (by simp [NumberBoundary])
  simp only [List.append_nil] at hp
  simp [parseCanonical, hr.2.1, hp, hc, hr, Bind.bind, Option.bind]


@[simp] theorem ascii_nil : Ascii [] := by simp [Ascii]
@[simp] theorem ascii_cons (b : UInt8) (s : Bytes) :
    Ascii (b :: s) ↔ b.toNat < 128 ∧ Ascii s := by simp [Ascii]
@[simp] theorem ascii_append (a b : Bytes) : Ascii (a ++ b) ↔ Ascii a ∧ Ascii b := by
  simp [Ascii, or_imp, forall_and]

theorem escapeByte_ascii (b : UInt8) (hb : b.toNat < 128) : Ascii (escapeByte b) := by
  generalize hn : b.toNat = n at hb
  have beq : b = UInt8.ofNat n := by simp [← hn]
  subst b
  interval_cases n <;> simp [Ascii, escapeByte, hex]

theorem string_ascii (s : Bytes) (ha : Ascii s) : Ascii (serializeString s) := by
  have h : Ascii (s.flatMap escapeByte) := by
    intro b hb
    obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
    exact escapeByte_ascii c (ha c hc) b hb
  simpa [serializeString] using h

theorem number_ascii (s : Bytes) (hn : canonicalNumber s = true) : Ascii s := by
  intro b hb
  have h := (canonical_number_chars s hn).2 b hb
  simp only [numberChar, digit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with h | h
  · omega
  · subst b
    decide

theorem serialize_ascii (t : JsonAST) (ht : IsCanonicalAST t) :
    Ascii (serializeCanonical t) := by
  apply JsonAST.rec
    (motive_1 := fun t => IsCanonicalAST t → Ascii (serializeCanonical t))
    (motive_2 := fun xs => canonicalArray xs = true → Ascii (arrayBytes xs))
    (motive_3 := fun xs => canonicalObject xs = true → Ascii (objectBytes xs))
    (motive_4 := fun kv => IsCanonicalAST kv.2 → Ascii (serializeCanonical kv.2))
    _ _ _ _ _ _ _ _ _ _ _ t ht
  · intro s ha
    exact string_ascii s (by simpa [IsCanonicalAST, canonicalAST, Ascii] using ha)
  · exact number_ascii
  · intro _
    simp [serializeCanonical, Ascii]
  · intro b _
    cases b <;> simp [serializeCanonical, Ascii]
  · intro xs ih ha
    simpa [serializeCanonical] using ih ha
  · intro xs ih ha
    simpa [serializeCanonical] using ih ha
  · intro _
    simp [arrayBytes, Ascii]
  · intro x xs hx hxs ha
    have h := Bool.and_eq_true_iff.mp ha
    cases xs with
    | nil => simpa [arrayBytes] using hx h.1
    | cons y ys => simpa only [arrayBytes, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        ascii_append, ascii_cons] using And.intro (hx h.1) (And.intro (by decide) (hxs h.2))
  · intro _
    simp [objectBytes, Ascii]
  · intro kv xs hv hxs ha
    rcases kv with ⟨k,v⟩
    simp only [canonicalObject, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ha
    have hk := string_ascii k ha.1.1.1
    have hh := hv ha.1.1.2
    cases xs with
    | nil => simpa [objectBytes, and_assoc] using And.intro hk hh
    | cons q qs =>
      change Ascii (serializeString k ++ 58 :: serializeCanonical v ++
        44 :: objectBytes (q :: qs))
      simp only [ascii_append, ascii_cons]
      exact ⟨⟨hk, by decide, hh⟩, by decide, hxs ha.1.2⟩
  · intro k v ih
    exact ih

theorem accepted_ascii {bs : Bytes} {t : JsonAST} (h : parseCanonical bs = some t) :
    Ascii bs := by
  have hc := parseCanonical_sound h
  rw [hc.bytes]
  exact serialize_ascii t hc.canonical

theorem accepted_byte_roundTrip {bs : Bytes} {t : JsonAST}
    (h : parseCanonical bs = some t) : serializeCanonical t = bs :=
  (parseCanonical_sound h).bytes.symm

end AlgebraicCertificateSyntax
