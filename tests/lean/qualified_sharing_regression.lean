import Verification.CryptoQualifiedDealerSharing
open Polynomial CryptoQualifiedDealerSharing
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
noncomputable def dp (d : Bool) : (ZMod 7)[X] := if d then C 2 + C 2 * X else C 1 + X
example : CryptoQualifiedDealerSharingSuite := verification_suite
example : (aggregatePoly Finset.univ dp).eval 0 = 3 := by
  norm_num [aggregatePoly, dp]
example : (aggregatePoly Finset.univ dp).natDegree < 2 := by
  apply aggregate_degree _ _ (by decide)
  intro d _
  cases d <;> simp only [dp, Bool.false_eq_true, ↓reduceIte] <;> compute_degree!
example : (aggregatePoly ({false} : Finset Bool) dp).eval 0 ≠
    (aggregatePoly Finset.univ dp).eval 0 := by
  norm_num [aggregatePoly, dp]
  decide
example : (5 + 1 : ZMod 7) + (4 - 1) = 5 + 4 := cancelling_errors 5 4 1
example (Q : Finset Bool) (d : Bool) (hd : d ∉ Q) (h : (dp d).eval 0 ≠ 0) :
    (aggregatePoly (insert d Q) dp).eval 0 ≠ (aggregatePoly Q dp).eval 0 :=
  inserted_dealer_changes_secret Q dp d hd h
