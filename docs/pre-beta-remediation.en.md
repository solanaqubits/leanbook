# Pre-beta remediation: stage 1

Base: `e6862fc845f5829ce871226159346723fd677da6`, including the correction
`444e9e4` and the experimental normalization refinement. This is a local
infrastructure candidate, not a qualified beta release. The production
normalizer is unchanged.

## Invocation inventory

`python3 tools/inventory_lean_invocations.py PATH` reproduces the historical
audit search and classifies supplemental tracked text separately. On the base:

| Historical category | Line matches |
| --- | ---: |
| Release/CI gate | 2 |
| Test-driver candidates | 220 |
| Tool/generated-input driver candidates | 8 |
| Runtime queries (`--version`, `--print-prefix`) | 2 |
| Total in 183 files | 232 |

There are also 155 supplemental documentation/comment/help-text matches.
These are textual candidates, not 232 proved executable compilation bypasses.
Dynamic argument construction and multiline calls still require review; this
inventory is not an exhaustive call-graph analysis or a new policy gate.
The intentional unconfigured negative control in the new regression test must
remain distinguishable from production elaboration.

## Implemented scope

- `tools/lean_invoke.py` builds configured `lake lean FILE -- ...` commands.
  The release registry audit and CI qutrit step now use it.
- The release build explicitly requests the root and every audited source under
  `Verification/`, including modules outside the root import closure. The
  independent auditor remains `lake env AUDITOR`: it is not a Lean elaboration.
- Six new targeted tests include dependency-free live Lake probes for option
  enforcement and a bad module omitted from root imports. Nine existing release
  evidence tests are retained.

## Required subsequent work

Stage 1 does **not** enforce a clean project build. The current release-evidence
validator must not be treated as the completed revised beta gate. Before a new
qualification, implement and test:

1. An initially empty project artifact graph, preserving external dependency
   artifacts; explicit project-source/target coverage, Built/Replayed accounting
   and final artifact hashes. A nonzero fresh count alone is insufficient.
2. Migration of remaining executable drivers and their fixtures without relaxing
   project options; preserve intentional negative controls and historical docs.
3. Versioned SimLab host watchdog and a real container termination regression.
4. Full beta on the final candidate with required host dependencies and no
   unexpected test skips. These scoped tests do not establish beta qualification.
5. Two-phase release: qualify the exact candidate SHA locally and in hosted CI;
   publish an immutable annotated tag on that SHA; verify tag CI separately
   before final release qualification. No publication is performed by this patch.

Cached dependencies and newly compiled project modules must be reported
separately. Repeated performance experiments and full ALCC tasks follow this
infrastructure qualification; the diagnostic pilot does not justify production
replacement.
