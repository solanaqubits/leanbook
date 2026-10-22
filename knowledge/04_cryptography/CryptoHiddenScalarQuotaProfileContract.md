---
id: CryptoHiddenScalarQuotaProfileContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaProfileContract.lean
source_sha256: 775824dbe81fc4640d7a73e3b32e7fad48508bd3a0008c74f2befdcc3f04b7f4
novelty: not-assessed
status: reviewed
---

# Finite quota profile transfer with independent context checking

[Lean](../../Verification/CryptoHiddenScalarQuotaProfileContract.lean).
Epsilon242, cryptography/bulletproofs-ipa.

`exportProfile n p` materializes precisely p(0),...,p(n-1). `profileFunction xs`
extends the list with zeros. Here i indexes states and t indexes transitions.
The absorbing state n never reads p(n). This is a finite representation sufficient
for quota evolution, not serialization of an arbitrary function outside i<n.

`Matches n expected xs` requires exact length and coefficient equality against an
independently supplied expected profile. `matches_iff` equates this check with
xs = exportProfile n expected. Rational equality identifies 1/2 and 2/4; canonical
bytes remain a separate codec concern. Empty profiles are allowed for n=0.
Coefficients outside [0,1] are accepted: these are algebraic statements, and a
probability interpretation needs separate premises.

Induction on t, generalized over the initial state, proves `quotaLower_agrees`.
`quotaDeficit_agrees` and `quotaRow_agrees` then preserve deficits and entire rows
for every horizon and j when p and q agree on i<n. `validSnapshot_agrees` preserves
both exact row equality and failure over the entire inclusive prefix.

`restoreTransferred?` checks Matches before rerunning the existing full-prefix
restoration using the received list's function. The caller supplies n, expected,
j and epsilon independently. `transferred_isSome_iff` characterizes acceptance as
Matches and validity relative to expected. `transferred_output` also binds the
output cursor to the exact snapshot. `transferred_export` equates the Option
snapshot projections with original restoration, including refusal and bound/row.
It does not equate cursors with different dependent types literally.

API examples and registry projections accompany 288 executable cases with fixed
expectations calculated separately using Python Fraction. They cover n=0, zero,
fractional, negative and greater-than-one coefficients, varying j/epsilon/horizons,
extra coefficients and corrupted rows. A counterexample shows that the same initial
row cannot authenticate the profile; the explicit Matches check rejects substitution.
Verification is scoped, not a new full beta run. Novelty is not assessed.

No new wire or byte format for profiles, profile file adapter, provenance or trust
in expected is established. No practical CPU/RAM bound or external-process refinement
is proved. Coordinated replacement of expected and the list requires independent
trust to detect. Existing snapshots, codec and reader remain unchanged.
