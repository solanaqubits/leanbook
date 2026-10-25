/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.AlgebraicCertificateBound
import Verification.AlgebraicCertificateCompleteness

/-!
# Canonical ALCC bytes to a bound mathematical verdict

`none` means that decoding failed, not that a residual is nonzero.
`some false` refutes the supplied certificate, not the underlying implication.
Expected-passport provenance remains a caller invariant. No Python refinement.
-/
namespace AlgebraicCertificateVerify
open AlgebraicCertificateSyntax AlgebraicCertificateSchema AlgebraicCertificateKernel
open AlgebraicCertificateBound AlgebraicCertificateCompleteness
open scoped BigOperators

/-- Mathematical residual in the formal polynomial ring determined by the task's dimension. -/
noncomputable def delta (t : UnboundTask) : MvPolynomial (Fin t.1) ℚ :=
  denote t.2.2.1.target -
    ∑ i, denote (t.2.2.2.multipliers i) * denote (t.2.2.1.hypotheses i)

/-- Decode both streams, bind the certificate, then compute the typed kernel verdict. -/
def verifyCertificateBytes (bp bc : Bytes) : Option Bool := do
  let t ← decodeBoundTask bp bc
  return checkCert t.2.2.1 t.2.2.2

/-- Link the implementation's sparse residual with the specified ring expression. -/
theorem denote_residual_eq_delta (t : UnboundTask) :
    denote (residual t.2.2.1 t.2.2.2) = delta t := by
  simp [residual, delta, denote_combination, sub_eq_add_neg]

/-- Exactly the bound decoder's refusals propagate as `none`. -/
theorem verifyCertificateBytes_none_iff (bp bc : Bytes) :
    verifyCertificateBytes bp bc = none ↔ decodeBoundTask bp bc = none := by
  cases h : decodeBoundTask bp bc <;> simp [verifyCertificateBytes, h]

/-- Expose the same decoded task and its actual Boolean kernel verdict. -/
theorem verifyCertificateBytes_some_iff (bp bc : Bytes) (verdict : Bool) :
    verifyCertificateBytes bp bc = some verdict ↔ ∃ t,
      decodeBoundTask bp bc = some t ∧ checkCert t.2.2.1 t.2.2.2 = verdict := by
  cases h : decodeBoundTask bp bc <;> simp [verifyCertificateBytes, h]

/-- Successful acceptance implies binding and a zero residual for the same task. -/
theorem verifyCertificateBytes_true_sound {bp bc : Bytes}
    (h : verifyCertificateBytes bp bc = some true) :
    ∃ t, BoundTaskRel bp bc t ∧ delta t = 0 := by
  rcases (verifyCertificateBytes_some_iff bp bc true).mp h with ⟨t, ht, hc⟩
  refine ⟨t, decodeBoundTask_sound ht, ?_⟩
  exact sub_eq_zero.mpr (checkCert_sound t.2.2.1 t.2.2.2 hc)

/-- Rejection implies binding and a nonzero residual; no point witness is asserted. -/
theorem verifyCertificateBytes_false_sound {bp bc : Bytes}
    (h : verifyCertificateBytes bp bc = some false) :
    ∃ t, BoundTaskRel bp bc t ∧ delta t ≠ 0 := by
  rcases (verifyCertificateBytes_some_iff bp bc false).mp h with ⟨t, ht, hc⟩
  refine ⟨t, decodeBoundTask_sound ht, ?_⟩
  rw [← denote_residual_eq_delta]
  exact checkCert_false_sound t.2.2.1 t.2.2.2 hc

end AlgebraicCertificateVerify
