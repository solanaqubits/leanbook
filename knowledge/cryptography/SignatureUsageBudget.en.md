---
id: SignatureUsageBudget
language: en
section: cryptography
source: Verification/SignatureUsageBudget.lean
source_sha256: e77cb02a2d27ced45d5df70eb09526bab87f2a3c0df7146f4a2b6b2467ad0cbf
novelty: not-assessed
status: reviewed
---

# Irreversible signing tickets

An accepted allocation of `count` tickets starts at the old issued counter and advances it by exactly `count`. The key label, epoch and limit are preserved. Successive half-open allocations are disjoint. A failed signing attempt after allocation can consume its ticket. Applying this accounting model to a device requires exclusive, durable issuance for the same signing key.

[Theorem](../../Verification/SignatureUsageBudget.lean#L71)
