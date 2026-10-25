---
id: CryptoGroth16PairingEquation
language: en
section: cryptography
source: Verification/CryptoGroth16PairingEquation.lean
source_sha256: 0c76dac540a97f74de5c74d0b6ddda5a1a0384ea7b41e895afc4b0db64dfca68
novelty: not-assessed
status: reviewed
---

# Groth16 verification equation in distinct pairing groups

Proof A and C live in G1, B in G2, and verification compares values in GT. Nondegeneracy derives the equivalence between this equation on scalar-generated elements and the finite-field equation a*b = alpha*beta + x*gamma + c*delta. With nonzero delta, fixed A/B/input determine C's scalar uniquely. A compensating C term preserves the equation under scalar shifts of A and B. Public-input group linear combinations have an exact difference identity.

The model has no arithmetic circuit, QAP witness relation, knowledge extractor, random simulation distribution or cryptographic security game. Exposed scalar setup values can complete the equation for every input, so acceptance is not presented as SNARK soundness. Tests cover valid and invalid triples and the degeneracy of zero delta. Reference: [Groth, On the Size of Pairing-Based Non-interactive Arguments](https://discovery.ucl.ac.uk/id/eprint/1501201/). No concrete curve implementation or zero-knowledge claim follows.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [scalar_pair](../../Verification/CryptoGroth16PairingEquation.lean#L41)
- [equation_iff](../../Verification/CryptoGroth16PairingEquation.lean#L46)
- [exposed_scalar_completion](../../Verification/CryptoGroth16PairingEquation.lean#L54)
- [fixed_ab_c_unique](../../Verification/CryptoGroth16PairingEquation.lean#L61)
- [shifted_equation](../../Verification/CryptoGroth16PairingEquation.lean#L70)
- [public_input_difference](../../Verification/CryptoGroth16PairingEquation.lean#L82)
- [verification_suite](../../Verification/CryptoGroth16PairingEquation.lean#L96)
