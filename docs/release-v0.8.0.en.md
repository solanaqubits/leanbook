# v0.8.0 — ALCC byte verification and execution interface

Beta validation checkpoint containing the additive batch `proof-graphs/alcc-byte-verification`, based on the public
v0.7.48 snapshot. Eight modules, canonical-byte CLI, live regressions and English
knowledge cards are added. Existing public modules, formal contracts and toolchain
are preserved, except registry imports and the two additive certificate suite fields.

The companion public SimLab package provides the separate compiled runner,
portable content-pinned build helper and offline receipt consistency checker.
No private history, research archive, credentials, runtime PIN or machine-specific
execution logs are exported. The previous private proof bridge is preserved in its
own repository; this release does not claim to publish its Receipt-6 mode.

The release gate covers all public Lean sources, both axiom auditors, the registry,
and all local live tests, including the existing pinned SQLite target profile.
Hosted CI retains its explicitly narrower SQLite exclusions. See
`alcc-release.json` for source selection and the release validation asset for
actual completed checks. This is not an independent whole-system security audit.

The full pipeline proves positive and negative certificate-verdict soundness for
the modeled functions. Compiled execution, historical archive consistency and
per-instance Lean kernel proofs are distinct evidence levels. Expected-passport
provenance, Python correctness, OS effects, physical resource limits and SHA-256
collision resistance remain outside the proof. No operational service is enabled.
