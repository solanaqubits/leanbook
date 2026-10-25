import Verification.CryptoThresholdBLSGroup
open Polynomial CryptoBLSSignatureAggregationGroup CryptoThresholdBLSGroup
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
noncomputable def bs := CryptoBLSSignatureAggregationGroup.ConsistencyModel 7
noncomputable def bp : (ZMod 7)[X] := C 3 + C 2 * X
example : CryptoThresholdBLSGroupSuite := verification_suite
example : combine id ({1, 2} : Finset (ZMod 7)) (fun i => sign (bp.eval i) (1 : ZMod 7)) =
    sign (bp.eval 0) 1 :=
  interpolate_partials id Function.injective_id _ bp (by norm_num [bp]; compute_degree!) 1
example : Verify bs (1 : ZMod 7) (publicKey bs (bp.eval 0))
    (combine id {1, 2} (fun i : ZMod 7 => sign (bp.eval i) 1)) :=
  checked_threshold_verifies bs id Function.injective_id {1, 2} bp
    (by norm_num [bp]; compute_degree!) 1 _
    (fun i _ => individual_bls_verification bs (bp.eval i) 1)
example : ¬ Verify bs (1 : ZMod 7) (publicKey bs 3) 4 := by
  rw [individual_verification_iff]
  norm_num [sign]
  decide
example : Verify bs (0 : ZMod 7) (publicKey bs 3) 0 := zero_message_degeneracy bs _
example : combine id ({1} : Finset (ZMod 7)) (fun i => sign (bp.eval i) (1 : ZMod 7)) ≠
    sign (bp.eval 0) 1 := by
  norm_num [combine, CryptoShamirSecretSharingGroup.lagrange_coeff, sign, bp]
  decide
