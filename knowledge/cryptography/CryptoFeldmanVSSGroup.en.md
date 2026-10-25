---
id: CryptoFeldmanVSSGroup
language: en
section: cryptography
source: Verification/CryptoFeldmanVSSGroup.lean
source_sha256: 220ab7da704104e2233f8022e6d089940af553e9db9fe17ce894bde1f105ea13
novelty: not-assessed
status: reviewed
---

# Arbitrary-degree Feldman share consistency in prime-order groups

The algebraic core uses a field K, an additive K-module B, a generator G,
and a polynomial p of natural degree strictly below n. It publishes the first
n coefficient commitments C_j = p.coeff(j) • G. At coordinate x a supplied share y
is checked against y • G = sum_(j<n) x^j • C_j.

Evaluation commutes with coefficient commitments. Under injectivity of scalar
action on G, verification is equivalent to y = p.eval(x); a changed share is
rejected. Equal commitment vectors determine equal bounded-degree polynomials.
For the existing CyclicSetup over ZMod q with prime q, surjectivity additionally
shows that an arbitrary fixed commitment vector determines a unique polynomial.
All accepted shares for that vector therefore belong to the same polynomial,
even without assuming that its dealer was honest. Existence uses choice and is
not an efficient discrete-log decoding algorithm.

For injective participant coordinates and at least n selected indices, verified
shares reconstruct p.eval(0) by the existing field Lagrange theorem. The theorem
uses one fixed commitment vector. It does not establish authenticated broadcast,
agreement on that vector, a complaint protocol, availability or dealer exclusion.
Degree zero and the zero polynomial are covered for positive n. The natural-degree
bound deliberately does not accept n=0. Coordinates need not be nonzero for
reconstruction; at coordinate zero the share is the secret itself.

Commitments and verification respect addition. Different constant coefficients
produce different public group elements, so no information-theoretic secrecy
claim for the public commitments follows from Shamir's private-share secrecy.
The zero-generator counterexample accepts every share, documenting the need for
the injectivity premise. The scalar group over ZMod 7 is a consistency model,
not a cryptographically hard elliptic-curve implementation.

## Validation and integration

The registry exports consistency, uniqueness, reconstruction and arbitrary-vector
consistency. Live examples exercise a quadratic 3-of-4 instance over ZMod 7,
wrong shares, a truncated vector, a constant polynomial, a zero generator and
homomorphic composition. A separate negative compilation test attempts to prove
acceptance of a false share. Actual command results are recorded outside Git;
this card does not claim a whole-library checkpoint or production deployment.

Reference: [Feldman, A Practical Scheme for Non-interactive Verifiable Secret
Sharing (1987)](https://www.cs.umd.edu/~gasarch/TOPICS/secretsharing/feldmanVSS.pdf).
The formal result covers the share-consistency equation and reconstruction,
not every security or network claim of the paper. No novelty claim is made.

## Theorem links
- [evaluation_commutes](../../Verification/CryptoFeldmanVSSGroup.lean#L36)
- [honest_completeness](../../Verification/CryptoFeldmanVSSGroup.lean#L43)
- [verify_iff_evaluation](../../Verification/CryptoFeldmanVSSGroup.lean#L48)
- [accepted_share_unique](../../Verification/CryptoFeldmanVSSGroup.lean#L54)
- [shifted_share_rejected](../../Verification/CryptoFeldmanVSSGroup.lean#L59)
- [committed_polynomial_unique](../../Verification/CryptoFeldmanVSSGroup.lean#L66)
- [verified_reconstruction](../../Verification/CryptoFeldmanVSSGroup.lean#L77)
- [commitments_add](../../Verification/CryptoFeldmanVSSGroup.lean#L91)
- [combine_verified](../../Verification/CryptoFeldmanVSSGroup.lean#L95)
- [different_secrets_different_commitments](../../Verification/CryptoFeldmanVSSGroup.lean#L102)
- [zero_generator_accepts](../../Verification/CryptoFeldmanVSSGroup.lean#L110)
- [prime_field_soundness](../../Verification/CryptoFeldmanVSSGroup.lean#L121)
- [arbitrary_commitments_determine_polynomial](../../Verification/CryptoFeldmanVSSGroup.lean#L128)
- [arbitrary_verified_family_consistent](../../Verification/CryptoFeldmanVSSGroup.lean#L145)
- [verification_suite](../../Verification/CryptoFeldmanVSSGroup.lean#L182)
