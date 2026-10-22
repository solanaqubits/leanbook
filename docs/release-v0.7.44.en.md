# v0.7.44: canonical snapshots, bounded IO and finite profiles

This release publishes epsilon240–242 and the bounded snapshot reader/CLI:

- QCS/01 byte frames: canonical ULEB128 and reduced signed rationals, exact EOF,
  inclusive size/bound/row limits, proved round trip and inverse canonicality.
- Strict structured RatWire/QuotaSnapshotWire decoding: positive denominators and
  coprimality, rejection of reducible pairs and noncanonical zero, unconditional
  `decode w = some s` iff `encode s = w`, and certified cursor restoration.
- Finite profile transfer for precisely p(0),...,p(n-1), with checks against an
  independently supplied expected profile and proved restoration equivalence.
- Bounded read-only file IO and CLI: short-read handling, an EOF probe at the exact
  limit, deterministic reported IO failures and strict decoding only after EOF.

The registry contains 244 direct MasterSuite imports and 288 Lean sources,
including Verification.lean. Independent public verification includes
strict Lake compilation, an explicit qutrit Spec build, all public unittest tests
with live mode and a union transitive axiom audit. The conservative planner requires a full validation gate
for the new tools/ IO adapter: verify-all, registry and independent audits are
therefore included. Lake uses weakLeanArgs = ["-j1"] to bound per-file elaboration concurrency; this
resource-only option preserves kernel checks and build traces. Individual local
Lean checks also use one elaboration thread under
an 8 GiB process-group limit. The validation scope is beta-level; no new beta tag
or baseline checkpoint is allocated. Lake stays at 0.7.1 and the full public beta basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1).

[Byte format](quota-codec-v1.en.md) · [Reader/CLI](quota-snapshot-reader.en.md).

The structured codec, byte codec, semantic restoration and expected-context
checking are separate layers. Arbitrary rational coefficients are permitted;
probabilistic interpretations require additional premises. File IO is tested,
not a formal OS refinement. No provenance, authorization, universal performance
improvement or total runtime resource bound is established. Profile byte encoding
and profile file IO are not part of this release.
