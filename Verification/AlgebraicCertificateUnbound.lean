/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.AlgebraicCertificateSchema

/-!
# Canonical bytes to an unbound ALCC task

Composition of the verified syntax and schema decoders. No SHA-256, digest
comparison, external Python refinement or certificate-validity verdict.
-/
namespace AlgebraicCertificateUnbound
open AlgebraicCertificateSyntax AlgebraicCertificateSchema

/-- Independent composition of the two relational specifications. -/
def UnboundTaskRel (bp bc : Bytes) (t : UnboundTask) : Prop :=
  ∃ jp jc : JsonAST,
    CanonicalParseRel bp jp ∧ CanonicalParseRel bc jc ∧ SchemaDecodeRel jp jc t

/-- Both byte streams must be canonical and the decoded pair must satisfy the schema. -/
def decodeFromBytes (bp bc : Bytes) : Option UnboundTask := do
  let jp ← parseCanonical bp
  let jc ← parseCanonical bc
  decodeSchema jp jc

/-- Successful execution exposes the actual intermediate trees, not just existential syntax. -/
theorem decodeFromBytes_success_iff {bp bc : Bytes} {t : UnboundTask} :
    decodeFromBytes bp bc = some t ↔ ∃ jp jc,
      parseCanonical bp = some jp ∧ parseCanonical bc = some jc ∧
      decodeSchema jp jc = some t := by
  constructor
  · intro h
    cases hp : parseCanonical bp with
    | none => simp [decodeFromBytes, hp] at h
    | some jp =>
      cases hc : parseCanonical bc with
      | none => simp [decodeFromBytes, hp, hc] at h
      | some jc =>
        exact ⟨jp, jc, rfl, rfl, by
          simpa only [decodeFromBytes, hp, hc, Bind.bind, Option.bind] using h⟩
  · rintro ⟨jp, jc, hp, hc, ht⟩
    simpa only [decodeFromBytes, hp, hc, Bind.bind, Option.bind] using ht

/-- Functionality of the relation, independent of the implementation's execution. -/
theorem unboundTaskRel_deterministic {bp bc : Bytes} {a b : UnboundTask}
    (ha : UnboundTaskRel bp bc a) (hb : UnboundTaskRel bp bc b) : a = b := by
  rcases ha with ⟨pa, ca, hpa, hca, hsa⟩
  rcases hb with ⟨pb, cb, hpb, hcb, hsb⟩
  have hp := canonicalParse_deterministic hpa hpb
  have hc := canonicalParse_deterministic hca hcb
  subst pb
  subst cb
  exact schemaDecodeRel_deterministic hsa hsb

/-- End-to-end soundness for the Lean pipeline; the resulting task is still unbound. -/
theorem decodeFromBytes_sound {bp bc : Bytes} {t : UnboundTask}
    (h : decodeFromBytes bp bc = some t) : UnboundTaskRel bp bc t := by
  rcases decodeFromBytes_success_iff.mp h with ⟨jp, jc, hp, hc, ht⟩
  exact ⟨jp, jc, parseCanonical_sound hp, parseCanonical_sound hc, decodeSchema_sound ht⟩

theorem decodeFromBytes_unique {bp bc : Bytes} {a b : UnboundTask}
    (ha : decodeFromBytes bp bc = some a) (hb : decodeFromBytes bp bc = some b) : a = b :=
  unboundTaskRel_deterministic (decodeFromBytes_sound ha) (decodeFromBytes_sound hb)

/-- The input streams, not only the abstract values, are canonical serializations. -/
theorem unboundTaskRel_canonical_bytes {bp bc : Bytes} {t : UnboundTask}
    (h : UnboundTaskRel bp bc t) : ∃ jp jc,
      bp = serializeCanonical jp ∧ bc = serializeCanonical jc ∧
      IsCanonicalAST jp ∧ IsCanonicalAST jc ∧ SchemaDecodeRel jp jc t := by
  rcases h with ⟨jp, jc, hp, hc, ht⟩
  exact ⟨jp, jc, hp.bytes, hc.bytes, hp.canonical, hc.canonical, ht⟩

/-- Transport a known schema computation through bounded canonical serialization.
This is not a proof of completeness of the schema decoder. -/
theorem decodeFromBytes_serialized (jp jc : JsonAST)
    (hp : IsCanonicalAST jp) (hc : IsCanonicalAST jc)
    (rp : WithinResourceLimits jp) (rc : WithinResourceLimits jc) :
    decodeFromBytes (serializeCanonical jp) (serializeCanonical jc) = decodeSchema jp jc := by
  simp only [decodeFromBytes, parseCanonical_complete jp hp rp,
    parseCanonical_complete jc hc rc]
  rfl

/-- An executable positive control supplies an actual witness to the independent relation. -/
theorem accepted_has_relation {bp bc : Bytes}
    (h : (decodeFromBytes bp bc).isSome = true) : ∃ t, UnboundTaskRel bp bc t := by
  cases ht : decodeFromBytes bp bc with
  | none => simp [ht] at h
  | some t => exact ⟨t, decodeFromBytes_sound ht⟩

end AlgebraicCertificateUnbound
