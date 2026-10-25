import Verification.CryptoFeldmanVSSGroup

open CryptoFeldmanVSSGroup CryptoShamirSecretSharingGroup Polynomial
open scoped BigOperators
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private noncomputable def S : Setup 7 3 4 (ZMod 7) :=
  ConsistencyModel 7 3 4 (by decide) (by decide) (by decide)
private noncomputable def p : ShamirPoly (ZMod 7) 3 3 :=
  ⟨C 3 + C 2 * X + C 4 * X ^ 2, by compute_degree!, by simp⟩
private theorem injective_one : Function.Injective (fun x : ZMod 7 => x • (1 : ZMod 7)) := by
  intro x y h
  simpa only [smul_eq_mul, mul_one] using h

example : CryptoFeldmanVSSGroupSuite := verification_suite
example (x : ZMod 7) : Verify (K := ZMod 7) (1 : ZMod 7) 3
    (commitments (K := ZMod 7) 1 p.val) x (p.val.eval x) :=
  honest_completeness 1 p.val p.property.1 x
example : Verify (K := ZMod 7) (1 : ZMod 7) 3 (commitments (K := ZMod 7) 1 p.val) 1 2 := by
  rw [verify_iff_evaluation 1 injective_one p.val p.property.1]
  norm_num [p]
  decide
example : ¬ Verify (K := ZMod 7) (1 : ZMod 7) 3 (commitments (K := ZMod 7) 1 p.val) 1 3 := by
  rw [verify_iff_evaluation 1 injective_one p.val p.property.1]
  norm_num [p]
  decide
example (x : ZMod 7) :
    ¬ Verify (K := ZMod 7) (1 : ZMod 7) 3
      (commitments (K := ZMod 7) 1 p.val) x (p.val.eval x + 1) :=
  shifted_share_rejected 1 injective_one p.val p.property.1 x 1 one_ne_zero
example (shares : Fin 4 → ZMod 7)
    (h : ∀ i ∈ ({0, 2, 3} : Finset (Fin 4)),
      Verify (K := ZMod 7) (1 : ZMod 7) 3
        (commitments (K := ZMod 7) 1 p.val) (S.coordinates i) (shares i)) :
    ∑ i ∈ ({0, 2, 3} : Finset (Fin 4)),
      lagrange_coeff S.coordinates {0, 2, 3} i * shares i = 3 := by
  simpa [p] using verified_reconstruction 1 injective_one p.val p.property.1
    S.coordinates S.coordinates_injective {0, 2, 3} (by decide) shares h
example : Verify (K := ZMod 7) (1 : ZMod 7) 1 (commitments (K := ZMod 7) 1 (C (5 : ZMod 7))) 2 5 :=
  by
    simpa using (honest_completeness (1 : ZMod 7) (C (5 : ZMod 7))
      (n := 1) (by compute_degree!) 2)
example : Verify (K := ZMod 7) (0 : ZMod 7) 3 (fun _ => 0) 1 3 :=
  zero_generator_accepts (K := ZMod 7) 3 1 3
example : Verify (K := ZMod 7) (0 : ZMod 7) 3 (fun _ => 0) 1 4 :=
  zero_generator_accepts (K := ZMod 7) 3 1 4
-- The zero coordinate reveals the constant coefficient; no secrecy is claimed there.
example : p.val.eval 0 = 3 := p.property.2
-- Too short a commitment vector does not verify this quadratic's actual share.
example : ¬ Verify (K := ZMod 7) (1 : ZMod 7) 2 (commitments (K := ZMod 7) 1 p.val) 1 2 := by
  norm_num [Verify, evaluateCommitments, commitments, p, Finset.sum_range_succ]
  decide
example : commitments (K := ZMod 7) (1 : ZMod 7) (C 3) 0 ≠ commitments (K := ZMod 7) 1 (C 4) 0 := by
  apply different_secrets_different_commitments 1 injective_one
  norm_num
  decide
example : Verify (K := ZMod 7) (1 : ZMod 7) 3
    (fun j => commitments (K := ZMod 7) 1 p.val j +
      commitments (K := ZMod 7) 1 p.val j) 1 (2 + 2) := by
  apply combine_verified
  all_goals
    rw [verify_iff_evaluation 1 injective_one p.val p.property.1]
    norm_num [p]
    decide
example (C : ℕ → ZMod 7) :
    ∃ p : (ZMod 7)[X], p.natDegree < 3 ∧ ∀ x y,
      Verify (K := ZMod 7) (1 : ZMod 7) 3 C x y ↔ y = p.eval x := by
  simpa [CryptoSchnorrMultiSignaturesMuSigGroup.scalarSetup] using
    arbitrary_verified_family_consistent
      (CryptoSchnorrMultiSignaturesMuSigGroup.scalarSetup (q := 7)) 3 (by decide) C
