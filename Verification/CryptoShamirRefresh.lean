/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoFeldmanVSSGroup

/-! Zero-constant refresh masks preserve a secret and rerandomize its entire
polynomial fiber. No erasure, mobile-adversary or network guarantee is claimed. -/
noncomputable section
open Polynomial CryptoShamirSecretSharingGroup
namespace CryptoShamirRefresh
variable {K : Type*} [Field K] {t : ℕ} {s : K}

def refresh (p : ShamirPoly K t s) (r : ShamirPoly K t 0) : ShamirPoly K t s :=
  ⟨p.val + r.val,
   lt_of_le_of_lt (natDegree_add_le _ _) (max_lt p.property.1 r.property.1),
   by simp [p.property.2, r.property.2]⟩

theorem refresh_share (p : ShamirPoly K t s) (r : ShamirPoly K t 0) (x : K) :
    (refresh p r).val.eval x = p.val.eval x + r.val.eval x := by simp [refresh]

theorem refresh_secret (p : ShamirPoly K t s) (r : ShamirPoly K t 0) :
    (refresh p r).val.eval 0 = s := (refresh p r).property.2

/-- For each fixed old sharing, addition is a bijection from masks to new sharings. -/
def refreshEquiv (p : ShamirPoly K t s) : ShamirPoly K t 0 ≃ ShamirPoly K t s where
  toFun := refresh p
  invFun u := ⟨u.val - p.val,
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt u.property.1 p.property.1),
    by simp [u.property.2, p.property.2]⟩
  left_inv r := by apply Subtype.ext; simp [refresh]
  right_inv u := by apply Subtype.ext; simp [refresh]

def refreshLaw [Fintype K] [Fact (0 < t)] (p : ShamirPoly K t s) : PMF (ShamirPoly K t s) :=
  (PMF.uniformOfFintype (ShamirPoly K t 0)).map (refresh p)

theorem refresh_uniform [Fintype K] [Fact (0 < t)] (p : ShamirPoly K t s) :
    refreshLaw p = PMF.uniformOfFintype (ShamirPoly K t s) :=
  map_uniform_equiv (refreshEquiv p)

theorem old_sharing_independent [Fintype K] [Fact (0 < t)] (p p' : ShamirPoly K t s) :
    refreshLaw p = refreshLaw p' := by rw [refresh_uniform, refresh_uniform]

theorem sequential_refresh (p : ShamirPoly K t s) (r u : ShamirPoly K t 0) :
    refresh (refresh p r) u = refresh p (refresh r u) := by
  apply Subtype.ext
  exact add_assoc _ _ _

theorem commitment_update {B : Type*} [AddCommGroup B] [Module K B]
    (G : B) (p : ShamirPoly K t s) (r : ShamirPoly K t 0) (j : ℕ) :
    CryptoFeldmanVSSGroup.commitments G (refresh p r).val j =
    CryptoFeldmanVSSGroup.commitments G p.val j + CryptoFeldmanVSSGroup.commitments G r.val j :=
  CryptoFeldmanVSSGroup.commitments_add G p.val r.val j

/-- The zero mask is permitted but does not change any share; freshness needs randomness. -/
theorem zero_mask_unchanged (ht : 0 < t) (p : ShamirPoly K t s) :
    refresh p ⟨0, by simpa using ht, by simp⟩ = p := by
  apply Subtype.ext
  simp [refresh]

structure CryptoShamirRefreshSuite : Prop where
  preservation : ∀ (K : Type) [Field K] (t : ℕ) (s : K)
    (p : ShamirPoly K t s) (r : ShamirPoly K t 0), (refresh p r).val.eval 0 = s
  rerandomization : ∀ (K : Type) [Field K] [Fintype K] (t : ℕ) [Fact (0 < t)]
    (s : K) (p : ShamirPoly K t s), refreshLaw p = PMF.uniformOfFintype (ShamirPoly K t s)

theorem verification_suite : CryptoShamirRefreshSuite where
  preservation := fun _ _ _ _ p r => refresh_secret p r
  rerandomization := fun _ _ _ _ _ _ p => refresh_uniform p
end CryptoShamirRefresh
