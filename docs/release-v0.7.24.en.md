# v0.7.24 — hidden-scalar single causal path

This scoped release exports epsilon220, CryptoHiddenScalarSinglePathContract,
from private source e90a47c6020342c44762f29a22b7e81f041e9ea1.
The public tree has 220 direct MasterSuite imports and 264 byte-identical formal
Lean sources. Lake remains 0.7.1. The full public beta baseline remains
2419489245019fb16e32ffac641b9f88eea94126; no new full beta run is claimed.

## Execution and verification

The executable runner follows the existing epsilon215 model on one fixed tape,
using actual transitions and exact reachable snapshots. It produces one path,
not a fork family. At IPA depth zero, the eta response is the final scalar pair.
SinglePathProvenance records the origin of messages at every boundary.
The theorem accepted_iff_verifies establishes:

AcceptedRun iff there exists a ProducedTranscript accepted by compressedVerify.

Primitive aborts and malformed packets produce no transcript. A syntactically
complete transcript is retained even when the scalar or leaf equation fails;
such a result has accepted=false. Checks do not implement an early-stop policy,
and no resource refinement of an early-stopping external verifier is asserted.
Announcement and scalar-response prefix lemmas establish message causality.

## Finite acceptance laws

Explicit chronological prefix/suffix equivalences preserve every microseed
occurrence, including duplicate preimages of one decoded challenge. The exact
acceptance_eq_prefix_average identity supports heavy_prefix_lower. A positive
threshold additionally yields an actual accepted continuation with provenance.
Call decoding depends on exact snapshots; independence of microseeds does not
assert independence of decoded challenge marginals. Acquisition retry budgets
are deliberately unused by the single-path runner.

Regressions cover depths 0/1/2, e=0, aborts, malformed packets, complete rejected
transcripts, snapshot-dependent decoders and chronological cuts. With three
outer microseeds decoding to [0,0,1] and only e=0 continuing, acceptance and the
heavy fraction at threshold 1/2 are both 2/3; the conservative bound is 1/3.
Uniformizing the decoded image would incorrectly yield 1/2.

## Verification and boundaries

Independent public scoped verification runs Lake --wfail, selected live unittest
and one union transitive axiom audit through AxiomAudit. Publication evidence
records actual counts, commands and final source fingerprints. Allowed axioms:
propext, Classical.choice, Quot.sound. No native_decide shortcuts are used.

The bridge from heavy single-path prefixes to child acquisition densities and
recursive quota completion remains separate. No random-tape averaging, general
Bellare–Neven theorem, Fiat–Shamir/ROM, polynomial runtime, external-process
refinement or hardware execution is asserted. Existing collector ResourceTrace
bounds remain unchanged: exact Q/R formulas are Clean-only, other runs retain
actual traces and schedule bounds, and initial abort has Q=1, R=0.
Private materials and private repository ancestry are not exported.
