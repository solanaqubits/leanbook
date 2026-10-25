import Verification.CryptoGroth16PairingEquation
open CryptoGroth16PairingEquation
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
noncomputable def gs := CryptoBLSSignatureAggregationGroup.ConsistencyModel 7
example : CryptoGroth16PairingEquationSuite := verification_suite
example : Verify gs (scalarKey gs 1 2 3 4)
    ((1 : ZMod 7) • gs.source₁.generator) (scalarProof gs 2 3 2) := by
  rw [equation_iff]
  decide
example : ¬ Verify gs (scalarKey gs 1 2 3 4)
    ((1 : ZMod 7) • gs.source₁.generator) (scalarProof gs 2 3 3) := by
  rw [equation_iff]
  decide
example (x a b : ZMod 7) : Verify gs (scalarKey gs 1 2 3 4) (x • gs.source₁.generator)
    (scalarProof gs a b ((a * b - 1 * 2 - x * 3) / 4)) :=
  exposed_scalar_completion gs 1 2 3 4 x a b (by decide)
example (c : ZMod 7) : Verify gs (scalarKey gs 1 2 3 0) ((1 : ZMod 7) • gs.source₁.generator)
    (scalarProof gs 1 5 c) := by
  rw [equation_iff]
  norm_num
example (r s : ZMod 7) : (2 + r) * (3 + s) = 1 * 2 + 1 * 3 +
    (2 + (2 * s + r * 3 + r * s) / 4) * 4 :=
  shifted_equation 1 2 3 4 1 2 3 2 r s (by decide) (by decide)
