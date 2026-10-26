# Reservoir indexing and package identity

## Current check: 2026-10-26

The public repository is [solanaqubits/leanbook](https://github.com/solanaqubits/leanbook).
Its Lake package identifier remains `lean-verification-components`. Repository
renaming and package renaming are different operations: keeping this identifier
preserves existing dependency declarations. Lake package version `0.7.1` and
checkpoint tags follow the separate [version policy](../VERSIONING.md); neither
is an established cause of the missing Reservoir entry.

The canonical `homepage` in `lakefile.toml` now points to `solanaqubits/leanbook`.
No package identifier, dependency revision, toolchain, compiler option, proof,
build target or published tag was changed by this metadata correction.

| Check | Observed result |
|---|---|
| Public source | GitHub API: `private=false`, repository ID `1366429017` |
| Fork/template origin | `fork=false`; `template_repository=null` |
| Root manifest | Tracked `lake-manifest.json` retrievable through GitHub Contents API |
| License | GitHub recognizes `Apache-2.0` |
| Stars | 3 at inspection |
| Lake integration | `lake reservoir-config 1.0.0` succeeds; `doIndex=true` |
| Package page | `@solanaqubits/lean-verification-components`: HTTP 404 |
| Repository-name page | `@solanaqubits/leanbook`: HTTP 404 |
| Package metadata API | `/api/v1/packages/solanaqubits/lean-verification-components`: HTTP 404 |

This establishes metadata eligibility and absence at the checked endpoints,
not Reservoir acceptance or a successful Reservoir build. Our qualified
[v0.10.0 checkpoint](https://github.com/solanaqubits/leanbook/releases/tag/v0.10.0)
has its own verification evidence; GitHub CI is not a Reservoir build result.

## Discovery diagnosis and follow-up

[Official inclusion criteria](https://reservoir.lean-lang.org/inclusion-criteria)
describe automatic indexing, normally approximately daily, and recommend an
upstream issue if an eligible package remains missing for several days. Our
historical check below already recorded the missing page on 2026-10-07.

At Reservoir commit `a5774ea3b51fef4a496f35c791cfa660c914454f`,
[`query_lake_repos`](https://github.com/leanprover/reservoir/blob/a5774ea3b51fef4a496f35c791cfa660c914454f/scripts/utils/repo.py)
uses GitHub Code Search with `filename:lake-manifest.json path:/`.
A repository-scoped query returned no results with `incomplete_results=true`,
while direct retrieval of our manifest succeeded. This is a possible discovery
failure, not a proven root cause; incomplete search results cannot establish
that GitHub has permanently excluded the repository.

The same upstream revision has no explicit exclusion for our repository in
`scripts/package-exclusions.txt`. Its registration API requires a Reservoir
administrator token; it is not a public self-service registration endpoint.

Useful read-only checks:

```bash
lake reservoir-config 1.0.0
lake --wfail check-build
gh api repos/solanaqubits/leanbook
gh api repos/solanaqubits/leanbook/contents/lake-manifest.json
curl --fail-with-body \
  https://reservoir.lean-lang.org/api/v1/packages/solanaqubits/lean-verification-components
```

The last command is expected to fail while the package is absent. Successful
local metadata extraction does not register the package. Inclusion must be
confirmed by a subsequent registry response; any upstream report and response
should be recorded separately rather than inferred from a local correction.

## Historical check: v0.5.12 release candidate

The following record describes 2026-10-07 and the previous repository name.
It is retained as historical evidence, not the current publication status.


Checked 2026-10-07 while preparing v0.5.12 from public baseline c4d6d779552d5b52b71778464f2048f0fa22c4a8 and private Simon snapshot 8a58301154937e277e38e417dda503cff403e1b6. Metadata readiness and registry acceptance are separate results. The public validation is recorded in [release v0.5.12](release-v0.5.12.en.md).

## Inclusion criteria

[Reservoir's official criteria](https://reservoir.lean-lang.org/inclusion-criteria) specify automatic GitHub indexing, normally approximately daily. They require public non-fork sources (template-generated repositories are also excluded), a root lake-manifest.json, a GitHub-recognized OSI license, and at least two stars.

| Check | Observed result |
|---|---|
| Public source | GitHub API private=false |
| Fork/template origin | fork=false; no template_repository reported |
| Root manifest | lake-manifest.json present, with pinned dependency revisions |
| License | GitHub recognizes Apache-2.0; LICENSE exists; lakefile licenseFiles=["LICENSE"] |
| Stars | 3 at inspection time |
| Package metadata | name, version, description, keywords, homepage, license all present |
| Toolchain/dependency pin | Lean v4.33.1 and Mathlib v4.33.1 retained |
| Release candidate | v0.5.12; the publication requires all checks and an atomic main/tag push |
| Registry visibility | Public package page returned HTTP 404 at inspection time; inclusion is not confirmed |

GitHub API: https://api.github.com/repos/solanaqubits/lean-verification-components

Package page checked: https://reservoir.lean-lang.org/@solanaqubits/lean-verification-components

The metadata already meets the requested shape. The release updates version to 0.5.12. The existing descriptive metadata, license, toolchain and dependency pins are retained. The homepage points to the public repository. Reservoir metadata guidance permits a homepage; it does not make all descriptive fields independent hard inclusion criteria.

## Commands and limits

The installed Lake v5.0.0-src+819816b (Lean 4.33.1) documents `lake pack` as archiving existing build outputs: it does not build, validate source metadata, submit a package or prove acceptance. No undocumented `reservoir-cli` registration step is claimed. See [Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

Readiness requires strict builds on the pinned toolchain and a root default library target, both covered by the public release verification and by the fresh export checks recorded in [Simon validation](simon-verification.en.md). No toolchain upgrade is inferred from the registry's newer releases.

Status: the inspected public repository meets the listed observable inclusion criteria; indexing remains unconfirmed. Recheck the page after the automatic indexing interval. If it remains absent for several days, the official criteria suggest filing a registry issue. No issue, message or registration request was sent by this task. The separate release procedure authorizes publication of v0.5.12; it does not register or guarantee Reservoir acceptance.
