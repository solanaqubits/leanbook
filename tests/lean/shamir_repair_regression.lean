import Verification.CryptoShamirShareRepair
open Polynomial CryptoShamirShareRepair
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
noncomputable def sp : (ZMod 7)[X] := C 3 + C 2 * X
example : CryptoShamirShareRepairSuite := verification_suite
example : repair id ({1, 2} : Finset (ZMod 7)) (fun i => sp.eval i) 3 = sp.eval 3 :=
  repair_evaluations id Function.injective_id {1, 2} sp (by norm_num [sp]; compute_degree!) 3
example : repair id ({1, 2} : Finset (ZMod 7)) (fun i => sp.eval i) 3 = 2 := by
  calc
    _ = sp.eval 3 := repair_evaluations id Function.injective_id {1, 2} sp
      (by norm_num [sp]; compute_degree!) 3
    _ = 2 := by norm_num [sp]; decide
example : repair id ({1, 2} : Finset (ZMod 7)) (fun i => sp.eval i) 0 = 3 := by
  calc
    _ = sp.eval 0 := repair_evaluations id Function.injective_id {1, 2} sp
      (by norm_num [sp]; compute_degree!) 0
    _ = 3 := by norm_num [sp]
example : repair id ({1} : Finset (ZMod 7)) (fun i => sp.eval i) 3 ≠ sp.eval 3 := by
  norm_num [repair, weight, sp]
  decide
example (e : ZMod 7) (he : e ≠ 0) : (2 : ZMod 7) * (5 + e) ≠ 2 * 5 :=
  contribution_error 2 5 e (by decide) he
