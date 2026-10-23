# Isolated SQLite WAL-reset backport reproduction

These are reviewed source tools, patch and vendor-source hashes from the qualified
private experiment. No vendored source tree or binary is redistributed. Supply an
authenticated vendor source matching source-manifest.json; rebuild.py copies it into
a new directory, applies the patch with zero fuzz and builds baseline/patched files.
It never performs make install. Build prefix-map path is redacted to /build; exact
binary reproducibility is NOT claimed. Do not substitute a new binary under an old
hash. ABI, Python loading, differential race controls and runtime conformance must be
qualified on the target. Historical private results do not qualify a rebuilt library.

The fixture race controls and run_controls.py exercise finite traces, not universal
SQLite/VFS correctness. See ../../docs/provenance-test-setup.en.md. External Witness
NOT_CONNECTED; authorization blocked; Third Obligation OPEN.
