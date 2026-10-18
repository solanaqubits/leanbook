# v0.7.20 — Hidden scalar nested fork acquisition

This scoped release exports epsilon215,
`Verification.CryptoHiddenScalarForkAcquisitionContract`, from source snapshot
`ac4ca79ca884ed5d4ca76cbdf7dd2fb23828fb15`.
The registry has 215 direct MasterSuite imports and 259 formal Lean sources,
including Verification.lean. All 259 match the source snapshot byte for byte.

## Results and assumptions

`AdversaryModel` fixes one tape and deterministic transitions with representable
aborts. Snapshots retain tape position, challenge history and memory. The finite
collector restores before each candidate, stops at its quota and filters duplicates
only against already accepted branches. Failed calls may be retried using distinct
suffix schedules. Nested exhaustion is local; every terminal outcome retains its
resource log. Equal algebraic contexts do not identify different adversary states.

`acquire_provenance_sound` establishes actual transition provenance relative to
this model. `acquire_valid_compressed_fork` connects successful acquisition to
epsilon214. `acquire_and_extract_soundness` yields either a joint opening witness
with the required inner product or an explicit nonzero generator relation.
Six acquired trees have 6*4^k leaves; they are internal extractor objects, not the
single transmitted proof. No computational hardness assumption is introduced.

`clean_acquisition_exact` gives Q(k)=4+2(4^(k+1)-1), R(k)=Q(k)-1 for Clean,
rejection-free runs, which it also proves successful. Arbitrary successful and
failed runs have explicit schedule-only upper bounds; exact actual costs come
from ResourceTrace. InitialAdversaryAbort has Q=1,R=0. These are model-operation
counts, not CPU time or a bound on work hidden inside the step function.

`clean_schedule_probability_lower` counts clean schedules under explicit
sequential conditional bounds on actual trace tests. Successful retries can add
probability. `acquisition_probability_lower` separately supports retry histories
through an explicit operational realization premise. Neither theorem derives
local density from a global acceptance probability or automatically transfers
statement-indexed recurrences to snapshot-indexed execution.

## Public validation

The public epsilon/scoped plan for cryptography/bulletproofs-ipa runs strict
Lake build, live unittest, one union transitive declaration audit with strict
AxiomAudit, metadata, knowledge and whitespace checks. Allowed axioms are
`propext`, `Classical.choice`, `Quot.sound`. Private receipts do not certify this
public tree. The incremental build cache is retained.

New coverage: 37 Lean examples, one helper theorem and 36 executable scenarios.
Regressions cover depths 0,1,2 over F11; witness and relation branches; failed
calls retried with fresh suffixes; retained-key duplicate filtering; early exit;
state-dependent responses; retained failure logs; and a finite conditional
probability example with success probability one half.

Lake remains 0.7.1. The full public beta basis remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1); no new full beta run is claimed.

Provenance is model-relative. External-process refinement, density for arbitrary
adversaries, general Bellare–Neven rewinding bounds, Fiat–Shamir/ROM and formal
polynomial-time guarantees remain open. Mathematical novelty is not-assessed.
Only allowlisted source/integration/test metadata and English documentation are
exported; private materials and private Git ancestry are excluded.
