/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.AlgebraicCertificateUnbound
import Verification.AlgebraicCertificateSHA256

/-!
# BoundTask: canonical bytes, schema and passport digest

The specification uses the functional SHA-256 reference, whereas the decoder
uses its proved executable refinement. Expected-passport provenance is a caller
invariant. This layer does not check the polynomial identity or authorize execution.
-/
namespace AlgebraicCertificateBound
open AlgebraicCertificateSyntax AlgebraicCertificateSchema AlgebraicCertificateUnbound
open AlgebraicCertificateSHA256 (MessageDomain hexLower SHA256Bytes)

/-- Remove only the top-level field; retain every other field in its original position. -/
def removeProblemId : JsonAST → JsonAST
  | .object fs => .object (fs.filter fun kv => kv.1 != bytes "problem_id")
  | j => j

/-- Partial extraction avoids treating missing fields as equal valid digests. -/
def problemId : JsonAST → Option Bytes
  | .object fs => do
      let (_, .string b) ← fs.find? (fun kv => kv.1 == bytes "problem_id") | none
      pure b
  | _ => none

def passportBody (jp : JsonAST) : Bytes := serializeCanonical (removeProblemId jp)

/-- Structural view of object canonicality, with explicit ordering independent of parsing. -/
theorem canonicalObject_iff (fs : List (Bytes × JsonAST)) : canonicalObject fs = true ↔
    (∀ kv ∈ fs, kv.1.all (fun b => b.toNat < 128) = true ∧ canonicalAST kv.2 = true) ∧
    (fs.map Prod.fst).IsChain (· < ·) := by
  induction fs with
  | nil => simp [canonicalObject]
  | cons kv fs ih =>
    rcases kv with ⟨k, v⟩
    cases fs with
    | nil => simp [canonicalObject]
    | cons kv fs =>
      simp only [canonicalObject, Bool.and_eq_true, decide_eq_true_eq] at *
      simp only [List.mem_cons, forall_eq_or_imp, List.map_cons,
        List.isChain_cons_cons] at ih ⊢
      tauto

theorem canonicalObject_filter (fs : List (Bytes × JsonAST)) (keep : Bytes × JsonAST → Bool)
    (h : canonicalObject fs = true) : canonicalObject (fs.filter keep) = true := by
  rw [canonicalObject_iff] at h ⊢
  refine ⟨fun kv hm => h.1 kv (List.mem_of_mem_filter hm), ?_⟩
  rw [List.isChain_iff_pairwise, List.pairwise_map] at h ⊢
  exact List.Pairwise.filter keep h.2

/-- Removal preserves sorted unique keys and all canonical child values. -/
theorem removeProblemId_canonical {jp : JsonAST} (h : IsCanonicalAST jp) :
    IsCanonicalAST (removeProblemId jp) := by
  cases jp with
  | object fs => exact canonicalObject_filter fs _ h
  | _ => exact h

/-- A declarative hash assertion using the reference specification, not the decoder. -/
def PassportHashValid (jp : JsonAST) : Prop :=
  MessageDomain (passportBody jp) ∧ problemId jp =
    some (hexLower (AlgebraicCertificateSHA256.Spec.SHA256Bytes (passportBody jp)))

/-- Both identifiers exist and equal the digest of this very expected passport. -/
def BindingRel (jp jc : JsonAST) : Prop :=
  PassportHashValid jp ∧ problemId jc = problemId jp

/-- Independent composed relation; the same AST witnesses support schema and binding. -/
def BoundTaskRel (bp bc : Bytes) (t : UnboundTask) : Prop :=
  ∃ jp jc, CanonicalParseRel bp jp ∧ CanonicalParseRel bc jc ∧
    SchemaDecodeRel jp jc t ∧ BindingRel jp jc

/-- Explicit FIPS length guard, then passport self-hash and certificate identifier. -/
def bindingCheck (jp jc : JsonAST) : Bool :=
  decide (MessageDomain (passportBody jp)) &&
    (problemId jp == some (hexLower (SHA256Bytes (passportBody jp)))) &&
    (problemId jc == problemId jp)

theorem bindingCheck_iff (jp jc : JsonAST) : bindingCheck jp jc = true ↔ BindingRel jp jc := by
  simp only [bindingCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    AlgebraicCertificateSHA256.sha256_refines, BindingRel, PassportHashValid]

def decodeBoundTask (bp bc : Bytes) : Option UnboundTask := do
  let jp ← parseCanonical bp
  let jc ← parseCanonical bc
  let t ← decodeSchema jp jc
  if bindingCheck jp jc then some t else none

theorem decodeBoundTask_success_iff {bp bc : Bytes} {t : UnboundTask} :
    decodeBoundTask bp bc = some t ↔ ∃ jp jc,
      parseCanonical bp = some jp ∧ parseCanonical bc = some jc ∧
      decodeSchema jp jc = some t ∧ bindingCheck jp jc = true := by
  cases hp : parseCanonical bp with
  | none => simp [decodeBoundTask, hp]
  | some jp =>
    cases hc : parseCanonical bc with
    | none => simp [decodeBoundTask, hp, hc]
    | some jc =>
      cases ht : decodeSchema jp jc with
      | none => simp [decodeBoundTask, hp, hc, ht]
      | some t' =>
        cases hb : bindingCheck jp jc <;>
          simp [decodeBoundTask, hp, hc, ht, hb]

/-- Successful execution of the Lean decoder proves binding to the supplied passport. -/
theorem decodeBoundTask_sound {bp bc : Bytes} {t : UnboundTask}
    (h : decodeBoundTask bp bc = some t) : BoundTaskRel bp bc t := by
  rcases decodeBoundTask_success_iff.mp h with ⟨jp, jc, hp, hc, ht, hb⟩
  exact ⟨jp, jc, parseCanonical_sound hp, parseCanonical_sound hc,
    decodeSchema_sound ht, (bindingCheck_iff jp jc).mp hb⟩

theorem boundTaskRel_unbound {bp bc : Bytes} {t : UnboundTask}
    (h : BoundTaskRel bp bc t) : UnboundTaskRel bp bc t := by
  rcases h with ⟨jp, jc, hp, hc, ht, _⟩
  exact ⟨jp, jc, hp, hc, ht⟩

/-- Relational uniqueness does not assume that either input was executed by the decoder. -/
theorem boundTaskRel_deterministic {bp bc : Bytes} {a b : UnboundTask}
    (ha : BoundTaskRel bp bc a) (hb : BoundTaskRel bp bc b) : a = b :=
  unboundTaskRel_deterministic (boundTaskRel_unbound ha) (boundTaskRel_unbound hb)

theorem boundTaskRel_digest {bp bc : Bytes} {t : UnboundTask}
    (h : BoundTaskRel bp bc t) : ∃ jp jc,
      bp = serializeCanonical jp ∧ bc = serializeCanonical jc ∧
      IsCanonicalAST (removeProblemId jp) ∧
      problemId jp = some (hexLower (AlgebraicCertificateSHA256.Spec.SHA256Bytes
        (passportBody jp))) ∧ problemId jc = problemId jp := by
  rcases h with ⟨jp, jc, hp, hc, _, hh, hi⟩
  exact ⟨jp, jc, hp.bytes, hc.bytes, removeProblemId_canonical hp.canonical, hh.2, hi⟩

/-- Concrete execution yields a witness without requiring decidable equality on tasks. -/
theorem accepted_has_relation {bp bc : Bytes}
    (h : (decodeBoundTask bp bc).isSome = true) : ∃ t, BoundTaskRel bp bc t := by
  cases ht : decodeBoundTask bp bc with
  | none => simp [ht] at h
  | some t => exact ⟨t, decodeBoundTask_sound ht⟩

end AlgebraicCertificateBound
