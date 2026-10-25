import Verification.CryptoPedersenVSSGroup
open Polynomial CryptoPedersenVSSGroup
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
noncomputable def ps : CryptoPedersenHomomorphicSum.Setup 7 (ZMod 7) :=
  CryptoPedersenHomomorphicSum.scalarSetup 2 (by decide)
noncomputable def vp : (ZMod 7)[X] := C 3 + C 2 * X
noncomputable def vr : (ZMod 7)[X] := C 4 + X
example : CryptoPedersenVSSGroupSuite := verification_suite
example (x : ZMod 7) : Verify ps 2 (commitments ps vp vr) x (vp.eval x) (vr.eval x) :=
  honest_completeness ps vp vr (by unfold vp; compute_degree!) (by unfold vr; compute_degree!) x
example : Verify ps 2 (commitments ps vp vr) 1 5 5 := by
  have h := honest_completeness ps vp vr (n := 2) (by unfold vp; compute_degree!) (by unfold vr; compute_degree!) 1
  convert h using 1 <;> norm_num [vp, vr]
example : ¬ Verify ps 2 (commitments ps vp vr) 1 6 (vr.eval 1) := by
  rw [fixed_blinding_soundness ps vp vr (by unfold vp; compute_degree!) (by unfold vr; compute_degree!)]
  norm_num [vp]
  decide
example (m m' : Fin 4 → ZMod 7) : coefficientLaw ps m = coefficientLaw ps m' :=
  coefficient_joint_hiding ps m m'
example : CryptoPedersenHomomorphicSum.commit ps 5 5 =
    CryptoPedersenHomomorphicSum.commit ps 3 6 := by
  norm_num [CryptoPedersenHomomorphicSum.commit, ps, CryptoPedersenHomomorphicSum.scalarSetup]
example : (5 : ZMod 7) ≠ 3 := by decide
example (x y z y' z' : ZMod 7) (C : ℕ → ZMod 7)
    (h : Verify ps 2 C x y z) (h' : Verify ps 2 C x y' z') (hn : y ≠ y') :
    z ≠ z' ∧ ps.h = ((y - y') * (z' - z)⁻¹) • ps.g :=
  conflicting_shares_extract_relation ps 2 C x y z y' z' h h' hn
