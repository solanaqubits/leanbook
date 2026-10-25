import Verification.CryptoShamirRefresh
open Polynomial CryptoShamirSecretSharingGroup CryptoShamirRefresh
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (0 < 2) := ⟨by decide⟩
noncomputable def rp : ShamirPoly (ZMod 7) 2 3 :=
  ⟨C 3 + C 2 * X, by compute_degree!, by simp⟩
noncomputable def rm : ShamirPoly (ZMod 7) 2 0 :=
  ⟨C 2 * X, by compute_degree!, by simp⟩
example : CryptoShamirRefreshSuite := verification_suite
example : (refresh rp rm).val.eval 0 = 3 := refresh_secret rp rm
example : (refresh rp rm).val.eval 1 = 0 := by
  norm_num [refresh, rp, rm]
  decide
example : rp.val.eval 1 ≠ (refresh rp rm).val.eval 1 := by
  norm_num [refresh, rp, rm]
  decide
example : (refreshEquiv rp).symm (refresh rp rm) = rm := (refreshEquiv rp).symm_apply_apply rm
example : refreshLaw rp = PMF.uniformOfFintype (ShamirPoly (ZMod 7) 2 3) := refresh_uniform rp
example (p' : ShamirPoly (ZMod 7) 2 3) : refreshLaw rp = refreshLaw p' := old_sharing_independent rp p'
example : refresh (refresh rp rm) rm = refresh rp (refresh rm rm) := sequential_refresh rp rm rm
example : (C (1 : ZMod 7) + X).eval 0 ≠ 0 := by norm_num
