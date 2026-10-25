/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBLSSignatureAggregationGroup
import Verification.CryptoShamirSecretSharingGroup

/-! Threshold BLS interpolation with checked partial signatures and typed pairings.
The key shares must come from one polynomial. This is not an unforgeability game,
hash-to-curve implementation, or distributed key generation protocol. -/
noncomputable section
open CryptoBLSSignatureAggregationGroup CryptoShamirSecretSharingGroup Polynomial
open scoped BigOperators
namespace CryptoThresholdBLSGroup
variable {q : ℕ} [Fact q.Prime]
variable {G₁ G₂ GT : Type} [AddCommGroup G₁] [Module (ZMod q) G₁]
  [AddCommGroup G₂] [Module (ZMod q) G₂] [AddCommGroup GT] [Module (ZMod q) GT]
variable {ι : Type} [DecidableEq ι]

def combine (ids : ι → ZMod q) (I : Finset ι) (partials : ι → G₁) : G₁ :=
  ∑ i ∈ I, lagrange_coeff ids I i • partials i

theorem interpolate_partials (ids : ι → ZMod q) (hi : Function.Injective ids)
    (I : Finset ι) (p : (ZMod q)[X]) (hp : p.natDegree < I.card) (H : G₁) :
    combine ids I (fun i => sign (p.eval (ids i)) H) = sign (p.eval 0) H := by
  simp only [combine, sign, smul_smul]
  rw [← Finset.sum_smul, field_lagrange_bridge ids hi I p hp]

theorem checked_partials_reconstruct (S : PairingSetup q G₁ G₂ GT)
    (ids : ι → ZMod q) (hi : Function.Injective ids) (I : Finset ι)
    (p : (ZMod q)[X]) (hp : p.natDegree < I.card) (H : G₁) (sig : ι → G₁)
    (hv : ∀ i ∈ I, Verify S H (publicKey S (p.eval (ids i))) (sig i)) :
    combine ids I sig = sign (p.eval 0) H := by
  rw [← interpolate_partials ids hi I p hp H]
  apply Finset.sum_congr rfl
  intro i hm
  rw [(individual_verification_iff S (p.eval (ids i)) H (sig i)).mp (hv i hm)]

theorem checked_threshold_verifies (S : PairingSetup q G₁ G₂ GT)
    (ids : ι → ZMod q) (hi : Function.Injective ids) (I : Finset ι)
    (p : (ZMod q)[X]) (hp : p.natDegree < I.card) (H : G₁) (sig : ι → G₁)
    (hv : ∀ i ∈ I, Verify S H (publicKey S (p.eval (ids i))) (sig i)) :
    Verify S H (publicKey S (p.eval 0)) (combine ids I sig) := by
  rw [checked_partials_reconstruct S ids hi I p hp H sig hv]
  exact individual_bls_verification S (p.eval 0) H

theorem quorum_independence (ids : ι → ZMod q) (hi : Function.Injective ids)
    (I J : Finset ι) (p : (ZMod q)[X]) (hI : p.natDegree < I.card)
    (hJ : p.natDegree < J.card) (H : G₁) :
    combine ids I (fun i => sign (p.eval (ids i)) H) =
    combine ids J (fun i => sign (p.eval (ids i)) H) := by
  rw [interpolate_partials ids hi I p hI, interpolate_partials ids hi J p hJ]

/-- Exact failure criterion, without claiming which individual participant is faulty. -/
theorem combined_verdict_iff (S : PairingSetup q G₁ G₂ GT)
    (ids : ι → ZMod q) (I : Finset ι) (s : ZMod q) (H : G₁) (sig : ι → G₁) :
    Verify S H (publicKey S s) (combine ids I sig) ↔ combine ids I sig = sign s H :=
  individual_verification_iff S s H (combine ids I sig)

/-- A zero message point makes a zero signature pass for every public key. -/
theorem zero_message_degeneracy (S : PairingSetup q G₁ G₂ GT) (pk : G₂) :
    Verify S 0 pk 0 := by simp [Verify]

structure CryptoThresholdBLSGroupSuite : Prop where
  recovery : ∀ (q : ℕ) [Fact q.Prime] (G₁ G₂ GT : Type)
    [AddCommGroup G₁] [Module (ZMod q) G₁] [AddCommGroup G₂] [Module (ZMod q) G₂]
    [AddCommGroup GT] [Module (ZMod q) GT] (S : PairingSetup q G₁ G₂ GT)
    (ι : Type) [DecidableEq ι] (ids : ι → ZMod q), Function.Injective ids →
    ∀ (I : Finset ι) (p : (ZMod q)[X]), p.natDegree < I.card → ∀ H sig,
    (∀ i ∈ I, Verify S H (publicKey S (p.eval (ids i))) (sig i)) →
    combine ids I sig = sign (p.eval 0) H

theorem verification_suite : CryptoThresholdBLSGroupSuite where
  recovery := fun _ _ _ _ _ _ _ _ _ _ _ S _ _ ids hi I p hp H sig hv =>
    checked_partials_reconstruct S ids hi I p hp H sig hv
end CryptoThresholdBLSGroup
