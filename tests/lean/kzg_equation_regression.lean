import Verification.CryptoKZGOpeningEquation
open Polynomial CryptoKZGOpeningEquation
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
noncomputable def ks := CryptoBLSSignatureAggregationGroup.ConsistencyModel 7
noncomputable def kp : (ZMod 7)[X] := C 3 + C 2 * X
example : CryptoKZGOpeningEquationSuite := verification_suite
example : Verify ks 4 (commit ks 4 kp) 1 (kp.eval 1) (commit ks 4 (quotient kp 1)) :=
  honest_opening ks kp 1 4
example : Verify ks 4 ((4 : ZMod 7) • ks.source₁.generator)
    1 5 ((2 : ZMod 7) • ks.source₁.generator) := by
  rw [equation_iff]
  decide
example : ¬ Verify ks 4 ((4 : ZMod 7) • ks.source₁.generator)
    1 6 ((2 : ZMod 7) • ks.source₁.generator) := by
  rw [equation_iff]
  decide
-- A different witness can forge the incorrect value when the trapdoor is exposed.
example : Verify ks 4 ((4 : ZMod 7) • ks.source₁.generator) 1 6
    ((((4 - 6) / (4 - 1)) : ZMod 7) • ks.source₁.generator) :=
  exposed_trapdoor_forges ks 4 4 1 6 (by decide)
example (w : ZMod 7) : ¬ Verify ks 4 ((4 : ZMod 7) • ks.source₁.generator)
    4 6 (w • ks.source₁.generator) := by
  rw [at_trapdoor_iff]
  decide
example (p : (ZMod 7)[X]) (z τ : ZMod 7) :
    p.eval τ - p.eval z = (quotient p z).eval τ * (τ - z) := quotient_identity p z τ
