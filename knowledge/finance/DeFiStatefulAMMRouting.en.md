---
id: DeFiStatefulAMMRouting
language: en
section: finance
source: Verification/DeFiStatefulAMMRouting.lean
source_sha256: e2e1798dcba012f57c21120978c6e456f29fa54ad745991d958ec96e46102be6
novelty: not-assessed
status: reviewed
---

# Reserve-updating routes with repeated pools

Pools carry positive real reserves and a fee multiplier in (0,1]. Each positive-amount trade changes the reserves, and reverse trades swap their orientation. The route interpreter threads both the market state and each output amount into the next hop. Repeated pool identifiers therefore use their updated state. By induction, every pool's reserve product is nondecreasing through any route. Pools not touched by the route are unchanged; outputs remain positive.

This is a numeric state-transition model. Matching token addresses and units across hops is a caller precondition; no wallet balances, asset conservation across mismatched token types, transaction atomicity, EVM execution or price oracle is certified. Tests distinguish two different pools from two uses of the same pool and verify a zero-fee forward/reverse round trip.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [swap_product](../../Verification/DeFiStatefulAMMRouting.lean#L36)
- [flip_product](../../Verification/DeFiStatefulAMMRouting.lean#L39)
- [trade_product](../../Verification/DeFiStatefulAMMRouting.lean#L44)
- [step_product](../../Verification/DeFiStatefulAMMRouting.lean#L64)
- [route_product](../../Verification/DeFiStatefulAMMRouting.lean#L71)
- [untouched_pool](../../Verification/DeFiStatefulAMMRouting.lean#L77)
- [route_output_positive](../../Verification/DeFiStatefulAMMRouting.lean#L86)
- [verification_suite](../../Verification/DeFiStatefulAMMRouting.lean#L95)
