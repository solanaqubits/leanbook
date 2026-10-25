---
id: CryptoKZGOpeningEquation
language: en
section: cryptography
source: Verification/CryptoKZGOpeningEquation.lean
source_sha256: 1ca49e1be85deebc533812dac64416ef0cc7ef4555c4032eabadbfb6cbc5bec7
novelty: not-assessed
status: reviewed
---

# Typed pairing equation for polynomial openings

The semantic commitment is p(tau) times the first source generator. Division by X-z constructs the witness polynomial; evaluating the quotient identity proves completeness of the typed pairing verification equation. For a fixed commitment and fixed witness the accepted value is unique. At z=tau the equation forces the committed evaluation.

The setup scalar tau is explicit for mathematical semantics. Knowing it allows construction of an accepted witness for any claimed value at z different from tau; this boundary is proved and tested, including a deliberately incorrect evaluation. Therefore the module does not assert computational evaluation binding, polynomial knowledge, hiding, trusted-setup security or an implementation from a bounded powers-of-tau SRS. Reference: [Kate, Zaverucha and Goldberg, Polynomial Commitments](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf). The formal scope is the opening equation, not the paper's security reductions.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [pairing_scalar](../../Verification/CryptoKZGOpeningEquation.lean#L27)
- [equation_iff](../../Verification/CryptoKZGOpeningEquation.lean#L32)
- [quotient_identity](../../Verification/CryptoKZGOpeningEquation.lean#L40)
- [honest_opening](../../Verification/CryptoKZGOpeningEquation.lean#L49)
- [fixed_witness_value_unique](../../Verification/CryptoKZGOpeningEquation.lean#L54)
- [exposed_trapdoor_forges](../../Verification/CryptoKZGOpeningEquation.lean#L61)
- [at_trapdoor_iff](../../Verification/CryptoKZGOpeningEquation.lean#L66)
- [verification_suite](../../Verification/CryptoKZGOpeningEquation.lean#L83)
