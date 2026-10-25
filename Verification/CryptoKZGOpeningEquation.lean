/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBLSSignatureAggregationGroup
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Typed pairing equation for polynomial openings. The semantic setup parameter
is explicit; exposing it permits forged evaluations. No binding or hardness claim. -/
noncomputable section
open Polynomial CryptoBLSSignatureAggregationGroup
namespace CryptoKZGOpeningEquation
variable {q : ℕ} [Fact q.Prime]
variable {G₁ G₂ GT : Type} [AddCommGroup G₁] [Module (ZMod q) G₁]
  [AddCommGroup G₂] [Module (ZMod q) G₂] [AddCommGroup GT] [Module (ZMod q) GT]
variable (S : PairingSetup q G₁ G₂ GT)

def commit (τ : ZMod q) (p : (ZMod q)[X]) : G₁ := p.eval τ • S.source₁.generator

def quotient (p : (ZMod q)[X]) (z : ZMod q) : (ZMod q)[X] := p /ₘ (X - C z)

def Verify (τ : ZMod q) (Cmt : G₁) (z y : ZMod q) (W : G₁) : Prop :=
  S.pair (Cmt - y • S.source₁.generator) S.source₂.generator =
    S.pair W ((τ - z) • S.source₂.generator)

theorem pairing_scalar (a b : ZMod q) :
    S.pair (a • S.source₁.generator) (b • S.source₂.generator) =
    (a * b) • S.pair S.source₁.generator S.source₂.generator := by
  simp only [S.pair.map_smul₂, (S.pair S.source₁.generator).map_smul, smul_smul]

theorem equation_iff (τ a z y w : ZMod q) :
    Verify S τ (a • S.source₁.generator) z y (w • S.source₁.generator) ↔
      a - y = w * (τ - z) := by
  rw [Verify, ← sub_smul, ← pairing_scalar_swap S (τ - z)]
  simp only [smul_smul]
  rw [pairing_generator_injective S |>.eq_iff, S.source₁.generator_bijective.1.eq_iff]
  rw [mul_comm]

theorem quotient_identity (p : (ZMod q)[X]) (z τ : ZMod q) :
    p.eval τ - p.eval z = (quotient p z).eval τ * (τ - z) := by
  have h := congrArg (Polynomial.eval τ) (modByMonic_add_div p (X - C z))
  simp only [modByMonic_X_sub_C_eq_C_eval, eval_add, eval_mul, eval_sub,
    eval_X, eval_C] at h
  dsimp [quotient]
  rw [← h]
  ring

theorem honest_opening (p : (ZMod q)[X]) (z τ : ZMod q) :
    Verify S τ (commit S τ p) z (p.eval z) (commit S τ (quotient p z)) := by
  rw [commit, commit, equation_iff]
  exact quotient_identity p z τ

theorem fixed_witness_value_unique (τ : ZMod q) (Cmt W : G₁) (z y y' : ZMod q)
    (h : Verify S τ Cmt z y W) (h' : Verify S τ Cmt z y' W) : y = y' := by
  have he := pairing_generator_injective S (h.trans h'.symm)
  have hs : y • S.source₁.generator = y' • S.source₁.generator := sub_right_injective he
  exact S.source₁.generator_bijective.1 hs

/-- Knowledge of the trapdoor gives an accepted witness for every claimed value off τ. -/
theorem exposed_trapdoor_forges (τ a z y : ZMod q) (hz : τ ≠ z) :
    Verify S τ (a • S.source₁.generator) z y
      (((a - y) / (τ - z)) • S.source₁.generator) := by
  rw [equation_iff, div_mul_cancel₀ _ (sub_ne_zero.mpr hz)]

theorem at_trapdoor_iff (τ a y w : ZMod q) :
    Verify S τ (a • S.source₁.generator) τ y (w • S.source₁.generator) ↔ a = y := by
  rw [equation_iff]
  simp [sub_eq_zero]

structure CryptoKZGOpeningEquationSuite : Prop where
  complete : ∀ (q : ℕ) [Fact q.Prime] (G₁ G₂ GT : Type)
    [AddCommGroup G₁] [Module (ZMod q) G₁] [AddCommGroup G₂] [Module (ZMod q) G₂]
    [AddCommGroup GT] [Module (ZMod q) GT] (S : PairingSetup q G₁ G₂ GT)
    (p : (ZMod q)[X]) (z τ : ZMod q),
    Verify S τ (commit S τ p) z (p.eval z) (commit S τ (quotient p z))
  trapdoor_boundary : ∀ (q : ℕ) [Fact q.Prime] (G₁ G₂ GT : Type)
    [AddCommGroup G₁] [Module (ZMod q) G₁] [AddCommGroup G₂] [Module (ZMod q) G₂]
    [AddCommGroup GT] [Module (ZMod q) GT] (S : PairingSetup q G₁ G₂ GT)
    (τ a z y : ZMod q), τ ≠ z →
    Verify S τ (a • S.source₁.generator) z y (((a - y) / (τ - z)) • S.source₁.generator)

theorem verification_suite : CryptoKZGOpeningEquationSuite where
  complete := fun _ _ _ _ _ _ _ _ _ _ _ S p z τ => honest_opening S p z τ
  trapdoor_boundary := fun _ _ _ _ _ _ _ _ _ _ _ S τ a z y h => exposed_trapdoor_forges S τ a z y h
end CryptoKZGOpeningEquation
