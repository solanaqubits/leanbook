/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.List.Basic

/-!
# Byte-oriented SHA-256

Functional transcription of FIPS 180-4 §§4.1.2, 4.2.2, 5.1.1, 5.2.1, 5.3.3, 6.2.2.
The specification uses indexed recurrences; execution uses accumulator loops.
Their refinement is proved for every input. FIPS applicability additionally requires
fewer than 2^61 bytes. No collision resistance or foreign-code refinement is asserted.
-/
namespace AlgebraicCertificateSHA256

abbrev Bytes := List UInt8
abbrev Word := UInt32

/-- Big-endian fixed-width encoding; callers specify the representable domain. -/
def beBytes (width value : Nat) : Bytes :=
  (List.range width).map fun i => UInt8.ofNat (value / 256 ^ (width - 1 - i) % 256)

def paddingZeros (length : Nat) : Nat := (119 - length % 64) % 64

def pad (message : Bytes) : Bytes :=
  message ++ [128] ++ List.replicate (paddingZeros message.length) 0 ++
    beBytes 8 (8 * message.length)

def MessageDomain (message : Bytes) : Prop := message.length < 2 ^ 61
instance (message : Bytes) : Decidable (MessageDomain message) := inferInstanceAs
  (Decidable (message.length < 2 ^ 61))

/-- Fixed 512-bit blocks, after padding. -/
def blocks (message : Bytes) : List Bytes :=
  let padded := pad message
  (List.range (padded.length / 64)).map fun i => (padded.drop (64 * i)).take 64

def rotr (x : Word) (n : Word) : Word := (x >>> n) ||| (x <<< (32 - n))
def ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def big0 (x : Word) : Word := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def big1 (x : Word) : Word := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def small0 (x : Word) : Word := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def small1 (x : Word) : Word := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

def roundConstants : List Word :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
   0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
   0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
   0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
   0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
   0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
   0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
   0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
   0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

structure State where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word
  deriving DecidableEq, Repr

def initial : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

def feedForward (s t : State) : State :=
  ⟨s.a + t.a, s.b + t.b, s.c + t.c, s.d + t.d,
   s.e + t.e, s.f + t.f, s.g + t.g, s.h + t.h⟩

def round (k w : Word) (s : State) : State :=
  let t1 := s.h + big1 s.e + ch s.e s.f s.g + k + w
  let t2 := big0 s.a + maj s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- Initial sixteen big-endian words. -/
def blockWords (block : Bytes) : List Word :=
  (List.range 16).map fun i =>
    UInt32.ofNat ((block.drop (4 * i)).take 4 |>.foldl (fun n b => 256 * n + b.toNat) 0)

/-- One step of the FIPS message schedule recurrence, at index `w.length`. -/
def scheduleStep (w : List Word) : List Word :=
  let t := w.length
  w ++ [small1 w[t - 2]! + w[t - 7]! + small0 w[t - 15]! + w[t - 16]!]

/-- Mathematical indexed recurrence: state after `n` steps. -/
def recurrence {α : Type} (step : Nat → α → α) (seed : α) : Nat → α
  | 0 => seed
  | n + 1 => step n (recurrence step seed n)

/-- Executable tail recursion, carrying the current index and accumulator. -/
def loop {α : Type} (step : Nat → α → α) : Nat → Nat → α → α
  | 0, _, acc => acc
  | remaining + 1, index, acc => loop step remaining (index + 1) (step index acc)

theorem loop_refines {α : Type} (step : Nat → α → α) (seed : α) (count index : Nat) :
    loop step count index (recurrence step seed index) = recurrence step seed (index + count) := by
  induction count generalizing index with
  | zero => simp [loop]
  | succ count ih =>
    change loop step count (index + 1) (recurrence step seed (index + 1)) = _
    rw [ih]
    congr 1
    omega

namespace Spec

def schedule (block : Bytes) : List Word :=
  recurrence (fun _ => scheduleStep) (blockWords block) 48

def compress (s : State) (block : Bytes) : State :=
  let w := schedule block
  feedForward s (recurrence (fun t => round roundConstants[t]! w[t]!) s 64)

def hashState (message : Bytes) : State :=
  let bs := blocks message
  recurrence (fun i s => compress s bs[i]!) initial bs.length

end Spec

def schedule (block : Bytes) : List Word := loop (fun _ => scheduleStep) 48 0 (blockWords block)

def compress (s : State) (block : Bytes) : State :=
  let w := schedule block
  feedForward s (loop (fun t => round roundConstants[t]! w[t]!) 64 0 s)

def hashState (message : Bytes) : State :=
  let bs := blocks message
  loop (fun i s => compress s bs[i]!) bs.length 0 initial

def digest (s : State) : Bytes :=
  [s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h].flatMap fun w => beBytes 4 w.toNat

/-- Functional byte-oriented FIPS specification. Outside MessageDomain no FIPS claim is made. -/
def Spec.SHA256Bytes (message : Bytes) : Bytes := digest (Spec.hashState message)

def SHA256Bytes (message : Bytes) : Bytes := digest (hashState message)

theorem schedule_refines (block : Bytes) : schedule block = Spec.schedule block := by
  exact loop_refines (fun _ => scheduleStep) (blockWords block) 48 0

theorem compress_refines (s : State) (block : Bytes) :
    compress s block = Spec.compress s block := by
  simp only [compress, Spec.compress, schedule_refines]
  exact congrArg (feedForward s)
    (loop_refines (fun t => round roundConstants[t]! (Spec.schedule block)[t]!) s 64 0)

theorem hashState_refines (message : Bytes) : hashState message = Spec.hashState message := by
  simp only [hashState, Spec.hashState, compress_refines]
  simpa only [Nat.zero_add, recurrence] using
    loop_refines (fun i s => Spec.compress s (blocks message)[i]!)
      initial (blocks message).length 0

/-- Universal refinement; tests are not used as premises. -/
theorem sha256_refines (message : Bytes) : SHA256Bytes message = Spec.SHA256Bytes message := by
  rw [SHA256Bytes, Spec.SHA256Bytes, hashState_refines]

theorem digest_length (s : State) : (digest s).length = 32 := by
  simp [digest, beBytes]

theorem sha256_length (message : Bytes) : (SHA256Bytes message).length = 32 :=
  digest_length _

def hexDigit (n : Nat) : UInt8 := UInt8.ofNat (if n < 10 then 48 + n else 87 + n)
def hexLower (bs : Bytes) : Bytes := bs.flatMap fun b => [hexDigit (b.toNat / 16),
  hexDigit (b.toNat % 16)]

theorem hexLower_length (bs : Bytes) : (hexLower bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [hexLower, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at *
    rw [ih]
    omega

theorem sha256_hex_length (message : Bytes) : (hexLower (SHA256Bytes message)).length = 64 := by
  rw [hexLower_length, sha256_length]

theorem paddingZeros_lt (length : Nat) : paddingZeros length < 64 :=
  Nat.mod_lt _ (by decide)

theorem padded_length_aligned (message : Bytes) : (pad message).length % 64 = 0 := by
  simp only [pad, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, beBytes, List.length_map, List.length_range, paddingZeros]
  have h := Nat.mod_lt message.length (by decide : 0 < 64)
  omega

theorem schedule_length (block : Bytes) : (schedule block).length = 64 := by
  rw [schedule_refines]
  have h : ∀ n, (recurrence (fun _ => scheduleStep) (blockWords block) n).length = 16 + n := by
    intro n
    induction n with
    | zero => simp [recurrence, blockWords]
    | succ n ih => simp only [recurrence, scheduleStep, List.length_append,
        List.length_cons, List.length_nil, ih]; omega
  exact h 48

/-- The smallest byte-aligned zero padding reaching the 448-bit position. -/
theorem paddingZeros_minimal (length k : Nat) (hk : k < paddingZeros length) :
    (length + 1 + k) % 64 ≠ 56 := by
  unfold paddingZeros at hk
  have h := Nat.mod_lt length (by decide : 0 < 64)
  omega

theorem message_bit_length {message : Bytes} (h : MessageDomain message) :
    8 * message.length < 2 ^ 64 := by
  unfold MessageDomain at h
  omega

def lowerHexByte (b : UInt8) : Bool :=
  (48 ≤ b.toNat && b.toNat ≤ 57) || (97 ≤ b.toNat && b.toNat ≤ 102)

theorem hexDigit_valid (n : Nat) (h : n < 16) : lowerHexByte (hexDigit n) = true := by
  unfold hexDigit
  split <;> simp only [lowerHexByte, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, UInt8.toNat_ofNat'] <;> omega

theorem hexLower_valid (bs : Bytes) : (hexLower bs).all lowerHexByte = true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := UInt8.toNat_lt b
    have hi := hexDigit_valid (b.toNat / 16) (by omega)
    have lo := hexDigit_valid (b.toNat % 16) (Nat.mod_lt _ (by decide))
    simpa only [hexLower, List.flatMap_cons, List.all_append, List.all_cons,
      List.all_nil, hi, lo, Bool.true_and] using ih

end AlgebraicCertificateSHA256
