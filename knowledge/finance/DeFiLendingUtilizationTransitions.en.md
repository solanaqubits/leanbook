---
id: DeFiLendingUtilizationTransitions
language: en
section: finance
source: Verification/DeFiLendingUtilizationTransitions.lean
source_sha256: 7ac4912985f27c8c00e51ea141887c51fdb0f0ebf497c65fe8e2542d7b72eb3d
novelty: not-assessed
status: reviewed
---

# Lending transitions conserve assets and change utilization

A state has nonnegative debt/reserves, cash covering reserves, and strictly positive net assets cash+debt-reserves. A borrow amount between zero and cash-reserves moves cash into debt. A repayment between zero and outstanding debt reverses that movement. Both preserve net assets and all state constraints. Utilization changes by exactly plus/minus amount/assets and stays between zero and one. Existing kink-model monotonicity then gives the corresponding borrow-rate directions; full repayment has zero utilization.

This model excludes interest accrual, default, liquidation, collateral and oracle-price changes. It refines an instantaneous utilization model rather than proving solvency of a lending protocol. Tests use exact rational balances, verify conservation and reject amounts beyond the available cash or outstanding debt.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [usage_eq_existing](../../Verification/DeFiLendingUtilizationTransitions.lean#L34)
- [usage_bounds](../../Verification/DeFiLendingUtilizationTransitions.lean#L40)
- [borrow_assets](../../Verification/DeFiLendingUtilizationTransitions.lean#L44)
- [repay_assets](../../Verification/DeFiLendingUtilizationTransitions.lean#L47)
- [borrow_usage](../../Verification/DeFiLendingUtilizationTransitions.lean#L50)
- [repay_usage](../../Verification/DeFiLendingUtilizationTransitions.lean#L56)
- [borrow_rate_increases](../../Verification/DeFiLendingUtilizationTransitions.lean#L62)
- [repay_rate_decreases](../../Verification/DeFiLendingUtilizationTransitions.lean#L69)
- [full_repayment_zero](../../Verification/DeFiLendingUtilizationTransitions.lean#L76)
- [verification_suite](../../Verification/DeFiLendingUtilizationTransitions.lean#L88)
