---
id: DeFiAMMIntegerSwap
language: en
section: finance
source: Verification/DeFiAMMIntegerSwap.lean
source_sha256: 184378ac7e10d79f1a411f8bc75178dd30b5a10fab287569614cd325e995ba29
novelty: not-assessed
status: reviewed
---

# Natural-number AMM rounding and reserve invariants

For positive reserves x,y and positive fee denominator d with numerator f at most d, output is floor(y*f*dx/(d*x+f*dx)). The module proves the exact quotient/remainder interval, output strictly below the reserve, and x*y <= (x+dx)*(y-output). Inputs and fees may be zero; zero-output dust is characterized by the numerator being smaller than the denominator.

Naturals are unbounded. No machine-word overflow or Solidity equivalence is asserted. The rounding interval fixes the arithmetic order explicitly. Concrete tests cover dust, zero fee multiplier, a large input, retained product and a multiplier greater than one that breaks the product guarantee.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [denominator_positive](../../Verification/DeFiAMMIntegerSwap.lean#L16)
- [rounding_bounds](../../Verification/DeFiAMMIntegerSwap.lean#L19)
- [output_lt_reserve](../../Verification/DeFiAMMIntegerSwap.lean#L25)
- [reserve_product_nondecreasing](../../Verification/DeFiAMMIntegerSwap.lean#L31)
- [dust_iff](../../Verification/DeFiAMMIntegerSwap.lean#L46)
- [zero_input](../../Verification/DeFiAMMIntegerSwap.lean#L51)
- [verification_suite](../../Verification/DeFiAMMIntegerSwap.lean#L58)
