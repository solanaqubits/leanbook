/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBLSSignatureAggregationGroup

/-! The Groth16 verifier equation in distinct source and target groups.
This model contains no circuit relation, knowledge extractor or zero-knowledge game.
Scalar witnesses describe group elements semantically, not a discrete-log algorithm. -/
noncomputable section
open CryptoBLSSignatureAggregationGroup
open scoped BigOperators
namespace CryptoGroth16PairingEquation
variable {q : ℕ} [Fact q.Prime]
variable {G₁ G₂ GT : Type} [AddCommGroup G₁] [Module (ZMod q) G₁]
  [AddCommGroup G₂] [Module (ZMod q) G₂] [AddCommGroup GT] [Module (ZMod q) GT]

structure Proof (G₁ G₂ : Type) where
  a : G₁
  b : G₂
  c : G₁

structure Key (G₁ G₂ : Type) where
  alpha : G₁
  beta : G₂
  gamma : G₂
  delta : G₂

def Verify (S : PairingSetup q G₁ G₂ GT) (vk : Key G₁ G₂) (input : G₁)
    (π : Proof G₁ G₂) : Prop :=
  S.pair π.a π.b = S.pair vk.alpha vk.beta + S.pair input vk.gamma + S.pair π.c vk.delta

def scalarKey (S : PairingSetup q G₁ G₂ GT) (α β γ δ : ZMod q) : Key G₁ G₂ :=
  ⟨α • S.source₁.generator, β • S.source₂.generator,
    γ • S.source₂.generator, δ • S.source₂.generator⟩

def scalarProof (S : PairingSetup q G₁ G₂ GT) (a b c : ZMod q) : Proof G₁ G₂ :=
  ⟨a • S.source₁.generator, b • S.source₂.generator, c • S.source₁.generator⟩

theorem scalar_pair (S : PairingSetup q G₁ G₂ GT) (a b : ZMod q) :
    S.pair (a • S.source₁.generator) (b • S.source₂.generator) =
    (a * b) • S.pair S.source₁.generator S.source₂.generator := by
  simp only [S.pair.map_smul₂, (S.pair S.source₁.generator).map_smul, smul_smul]

theorem equation_iff (S : PairingSetup q G₁ G₂ GT) (α β γ δ x a b c : ZMod q) :
    Verify S (scalarKey S α β γ δ) (x • S.source₁.generator) (scalarProof S a b c) ↔
    a * b = α * β + x * γ + c * δ := by
  unfold Verify scalarKey scalarProof
  simp only [scalar_pair, ← add_smul]
  exact (smul_left_injective (ZMod q) S.nondegenerate).eq_iff

/-- The equation can be solved using exposed scalar setup values; this is not SNARK soundness. -/
theorem exposed_scalar_completion (S : PairingSetup q G₁ G₂ GT)
    (α β γ δ x a b : ZMod q) (hδ : δ ≠ 0) :
    Verify S (scalarKey S α β γ δ) (x • S.source₁.generator)
      (scalarProof S a b ((a * b - α * β - x * γ) / δ)) := by
  rw [equation_iff, div_mul_cancel₀ _ hδ]
  ring

theorem fixed_ab_c_unique (S : PairingSetup q G₁ G₂ GT)
    (α β γ δ x a b c c' : ZMod q) (hδ : δ ≠ 0)
    (h : Verify S (scalarKey S α β γ δ) (x • S.source₁.generator) (scalarProof S a b c))
    (h' : Verify S (scalarKey S α β γ δ) (x • S.source₁.generator) (scalarProof S a b c')) :
    c = c' := by
  rw [equation_iff] at h h'
  exact mul_right_cancel₀ hδ (add_left_cancel (h.symm.trans h'))

/-- Shifting both proof sources has a determined compensating C term. No distribution claim. -/
theorem shifted_equation (α β γ δ x a b c r s : ZMod q) (hδ : δ ≠ 0)
    (h : a * b = α * β + x * γ + c * δ) :
    (a + r) * (b + s) = α * β + x * γ +
      (c + (a * s + r * b + r * s) / δ) * δ := by
  rw [add_mul c ((a * s + r * b + r * s) / δ) δ, div_mul_cancel₀ _ hδ]
  calc
    (a + r) * (b + s) = a * b + (a * s + r * b + r * s) := by ring
    _ = _ := by rw [h]; ring

def publicInput {ι : Type} (I : Finset ι) (base : G₁) (coeff : ι → G₁)
    (x : ι → ZMod q) : G₁ := base + ∑ i ∈ I, x i • coeff i

theorem public_input_difference {ι : Type} (I : Finset ι) (base : G₁)
    (coeff : ι → G₁) (x y : ι → ZMod q) :
    publicInput I base coeff x - publicInput I base coeff y =
      ∑ i ∈ I, (x i - y i) • coeff i := by
  simp only [publicInput, add_sub_add_left_eq_sub, sub_smul, Finset.sum_sub_distrib]

structure CryptoGroth16PairingEquationSuite : Prop where
  scalar_bridge : ∀ (q : ℕ) [Fact q.Prime] (G₁ G₂ GT : Type)
    [AddCommGroup G₁] [Module (ZMod q) G₁] [AddCommGroup G₂] [Module (ZMod q) G₂]
    [AddCommGroup GT] [Module (ZMod q) GT] (S : PairingSetup q G₁ G₂ GT)
    (α β γ δ x a b c : ZMod q),
    Verify S (scalarKey S α β γ δ) (x • S.source₁.generator) (scalarProof S a b c) ↔
    a * b = α * β + x * γ + c * δ

theorem verification_suite : CryptoGroth16PairingEquationSuite where
  scalar_bridge := fun _ _ _ _ _ _ _ _ _ _ _ S α β γ δ x a b c => equation_iff S α β γ δ x a b c
end CryptoGroth16PairingEquation
