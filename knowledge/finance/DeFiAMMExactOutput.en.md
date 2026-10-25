---
id: DeFiAMMExactOutput
language: en
section: finance
source: Verification/DeFiAMMExactOutput.lean
source_sha256: 2674df56e0aa6a9908f39519006361fd4bf57582c35274400b8676b288a23736
novelty: not-assessed
status: reviewed
---

# Exact-output inverse and minimum AMM input

For positive real input reserve and fee multiplier and a requested output strictly between zero and the output reserve, requiredInput is rx*dy/(gamma*(ry-dy)). The swap returns exactly dy on this input, and the two formulas are inverse on their valid domains. An input reaches at least dy if and only if it is at least requiredInput; exact equality uniquely determines the input.

The result uses real arithmetic, excluding token rounding, machine overflow, gas and deployed bytecode. The domain restriction is substantive: requesting the whole reserve gives a division-by-zero expression in the field model, not a feasible quote. Tests check exact rational-valued examples embedded in the reals, fee effects, insufficient inputs and this excluded boundary.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [required_positive](../../Verification/DeFiAMMExactOutput.lean#L16)
- [output_of_required](../../Verification/DeFiAMMExactOutput.lean#L21)
- [required_of_output](../../Verification/DeFiAMMExactOutput.lean#L30)
- [minimum_input_iff](../../Verification/DeFiAMMExactOutput.lean#L44)
- [exact_input_unique](../../Verification/DeFiAMMExactOutput.lean#L61)
- [verification_suite](../../Verification/DeFiAMMExactOutput.lean#L72)
