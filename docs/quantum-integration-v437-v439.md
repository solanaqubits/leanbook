# Quantum v4.37–v4.39 integration

This integration combines three checked local modules on public main
`a42c09d766bb6e2f32d4c1843b9de8a71a52df6c`. The candidate chain is
`acb520f3ad5e4a101b9f985a98ce450b642f0954` (v4.37),
`2437a0830903a1ad673b4e8c330219b3d22ee4ad` (v4.38), and
`df351face373012998d096d513c28120b9278bac` (v4.39).
All three formal module files, their tests, and the registry integration are
preserved byte-for-byte from the checked candidate. This integration adds shared
documentation; it changes no proof, toolchain, dependency or verification rule.

## Formal coverage

| Stage | Module | Named theorems | Named exports |
|---|---|---:|---:|
| v4.37 | QuantumNoisyBBPSSWTree | 26 | 34 |
| v4.38 | QuantumScheduledNoisyRepeater | 36 | 53 |
| v4.39 | QuantumNoisyRepeaterWitness | 26 | 32 |
| Total | Three modules | 88 | 119 |

These are code metrics, not counts of independent scientific results. The catalog
contains 400 modules across 12 sections, 404 library Lean files including nested
support sources and the root, and 354 direct MasterSuite imports. The registry
fields are `noisy_tree`, `scheduled_noisy` and `noisy_witness`.

The [v4.37 record](quantum-v4.37.md) constructs the unnormalized noisy BBPSSW
tree, proves D_n = p_n W(F_n) with p_(n+1) = p_n^2 P(F_n), and gives the exact
finite-depth post-swap recovery criterion. Post-depolarization preserves each
node's success probability; the complete tree weight depends on the noisy orbit.

The [v4.38 record](quantum-v4.38.md) composes spatial levels chronologically
using List.foldl and an independently updated matrix, weight and visibility.
The invariant connects these fields without recovering visibility by dividing a
matrix. Raw-pair resources are the product of 2^(m+1) over the schedule, with
multiplicity. Spatial segments number 2^(schedule length).

The [v4.39 record](quantum-v4.39.md) certifies gamma=19/20, w0=4/5 and schedule
[16,16] by rational interval chains checked in Lean. Both nonempty prefixes
strictly improve the initial visibility, and the second also improves the first.
Depth 16 is minimal at each of these two specific inputs. This is not global
schedule optimality. Four spatial segments consume 2^34 = 17179869184 leaves in
the fixed all-success resource tree. This count is neither success probability
nor expected consumption with retries. The ideal [4,2] witness uses gamma=1;
it is not a witness for gamma=19/20.

Swapping remains ideal. Noise acts on the retained pair after each BBPSSW step.
The conditional output is a normalized Werner state, generally mixed. Nonlinear
diagonal resource preparation is not claimed to be a linear CP map or cloning.
No asymptotic generation rate, noisy BSM model or optimal resource cost is claimed.

## Verification and publication boundaries

The integration gate uses scoped/gamma quantum-physics checks against the actual
public parent, including affected numeric-certificates and registry consumers.
It adds a complete incremental `lake build --wfail`, a pinned independent audit
of all compiled project declarations, and every local unittest module in the
qualified 12 GiB / 4 CPU / swap=0 container. Live Lean, SQLite and native crypto
checks are enabled. Metadata, knowledge links and whitespace are checked.
Only propext, Classical.choice and Quot.sound are allowed; sorryAx and
native-decide shortcuts are excluded.

The integration evidence records measured results, commands, source identities,
runtime limits and logs. Previous stage archives remain immutable. Candidate CI
must succeed, including verify-all, before a normal fast-forward of the same SHA
to main. The main push receives its own final CI receipt. Hosted profile skips
are reported separately from the required zero-skip local test run.

This publication creates no release tag and moves no existing tag. Leanbook
v1.0.0 and its assets remain unchanged. Incremental local checks and hosted
verify-all do not establish a new clean full-library beta checkpoint under
VERSIONING.md. Historical development-stage records retain their original scope.
