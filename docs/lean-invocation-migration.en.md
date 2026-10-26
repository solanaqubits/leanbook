# Configured Lean invocation migration

This local pre-beta remediation follows `200d40a4`. It does not qualify a beta
release, replace ALCC normalization, or publish any branch or tag.

## Scope and inventory

The earlier inventory counted 232 **text matches**, not all executable calls.
Two compilation sites in the gate/CI were already repaired; two matches were
informational. The remaining 228 compiler candidates were reviewed together
with Python AST list construction and dynamic argument assembly. This found
20 additional multiline calls: **248 migrated constructions**, across 201
Python files. The AST inventory also records one intentionally bare compiler
negative control and one informational query, for 250 rows in
[the migration inventory](lean-invocation-migration.json).

The groups distinguish strict positive drivers, negative-control consumers,
dynamic/tool argument assembly, and non-compiling queries. A shared helper can
serve both positive and negative consumers. This review and the static
regression check do not prove exhaustive coverage of arbitrary runtime command
construction, shell strings or future code.

## Invocation contract

`tools/lean_invoke.py` uses `lake lean FILE -- -j1 -DwarningAsError=true ...`.
This retains workspace options, including weak Mathlib linters, rather than
launching the compiler only within Lake's environment. Legacy argument lists
are translated by `lean_command`; only reviewed options are accepted. Output
paths (`-o`, `-c`), JSON diagnostics and native-library paths are retained.
Unknown options and warning-policy weakening are rejected.

For runtime clients, the command repeats the source after `--run`:
`lake lean FILE -- -j1 -DwarningAsError=true --run FILE ARGUMENTS`.
Lake passes its own source and setup arguments first; the repeated filename is
needed so Lean does not interpret the first runtime argument as its source.
Runtime arguments remain separate argv entries, including spaces and leading
dashes. Real tests exercise this behavior and artifact generation.

The one bare `lake env lean` compilation is an explicit tiny-project negative
control demonstrating that workspace `autoImplicit=false` is missed by the old
path. Version/prefix queries do not elaborate source and remain unchanged.
Existing verifier entry points already using configured Lake execution stay in
place. The Simon conformance input snapshot now includes the shared helper.

## Preserving fixture and refusal semantics

Configured execution exposed existing Mathlib style violations in fixtures.
The repairs wrap lines, add operator spacing, scope existing heartbeat budgets
per declaration, and retain their numeric values. Long registry projections use
an abbreviation for exactly the same explicitly specialized registry. Scoped
`classical` tactics replace a global Classical opening in the Marzullo fixture.
Layout-sensitive tactic blocks retain the same obligations and proof steps;
the Pedersen range `#eval` explicitly identifies its existing IO result type.
The threshold-quota proof uses an explicit `simp only` rule list before kernel
reduction, preserving the original goal while satisfying the flexible-tactic linter.
Exact `#eval` output comparisons use JSON diagnostics to distinguish returned
values from Mathlib’s informational hash-command note; unknown output is retained
and warnings/errors are rejected. Mixed heartbeat budgets are reviewed per section;
the generator utility refuses to collapse different limits into one.
Fixed data, expected algebraic outcomes and production `Verification/` sources
are retained.

The ALCC generators share a conservative fixture-layout utility and are checked
against their committed output. This utility is intended for these reviewed
fixtures, not arbitrary Lean code. Generated fixtures must still pass Lean.
Run generators as modules, for example `python3 -m tests.generate_alcc_bound_cases`.

ALCC false claims now require exit code 1 and JSON error diagnostics identifying
the expected failed `rfl` proof. An unrelated warning, import error or syntax
failure cannot count as successful falsification. Separate real probes exercise
valid code, false equality, unknown identifiers, syntax errors, missing imports
and warnings. The previously repaired Feldman controls retain their checks.
Runtime refusals (such as reader status 2) preserve their distinct protocol.

The qutrit and Simon checkers reflow three application/declaration boundaries
when rendering their probes, before substituting longer candidate names. Their
pinned templates, PIN hashes and mathematical contracts are unchanged. Tests
compare the complete whitespace-delimited token sequences before and after
rendering, and live tests accept both original and alternative proofs. Qutrit
mutations require the expected definition/statement mismatch diagnostic, rather
than any probe failure.

## Evidence boundaries

Validation logs and invocation records are kept outside the repository in
`/home/cyberg/worktrees/pre-beta-invocation-migration-evidence/`. Diagnostic
failures are retained alongside subsequent checks. The final closeout records
the tested source hashes, exact test totals, container limits and local commit.

Regression execution uses the pinned local Lean toolchain, a read-only shared
package cache, qualified archived SQLite and host libsodium in an offline
container. It does not install dependencies or re-run a clean Mathlib build.
The previous clean-project receipt belongs to `200d40a4`; it does not certify
these changed drivers. A final full beta gate and candidate CI remain separate
obligations. The last qualified beta checkpoint remains `v0.8.0`.

The local closeout distinguishes the complete regression run from subsequent
affected-test reruns. It records any intervening source changes explicitly;
passing tests on an earlier snapshot are not represented as one clean run of the
final tree. No new full beta qualification is inferred from these checks.
