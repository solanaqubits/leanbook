---
id: PrometheusCascadedFECBound
language: en
section: quantum-physics
source: Verification/PrometheusCascadedFECBound.lean
novelty: not-assessed
status: reviewed
source_sha256: 84f63cd2742baebcd9ffcfc26993c6dfb067c4bac269fbb4a27ff6c1aea91c4d
---

# Conditional IID RS/repetition cascade bound

[Section](README.md) · [Lean](../../Verification/PrometheusCascadedFECBound.lean)

Epsilon265. Five independent ternary slot observations use majority voting;
a tie including all erasures erases the bit. Any erased bit erases its byte.
Exact finite sums yield bit and byte outcome laws. For240 independent byte outcomes
with probabilities c,e,t, the PGF is(c+e*z+t*z²)^240. Weight equals2*errors+erasures.
For every rational z>1 the tail at205 is bounded by PGF/z^205. This is the rational
Chernoff form; no continuous infimum minimization is certified.

Lean proves the coarse tail bound<12/1000000 for both pe=6664/10000,
ps=34/3336 and the distinct rounded ps=10192/1000000. Tighter numerical intervals
live in SimLab. They are not substituted for the formal theorem.

failure_bound requires an explicit within-radius correctness premise. The actual
GF256/Berlekamp–Massey/Forney implementation and its minimum distance are not proved.
The arithmetic n-k+1=205 alone does not prove code distance. Tail probability is not
defined as actual packet error probability. wrong_valid_frame shows framing accepts
the correctly tagged alternative payload; no unconditional CRC2^-32 guarantee.

Proof: finite enumeration, normalized product laws, byte pushforward, PGF
factorization and pointwise indicator bound. Main declarations: five_mass_exact,
byte_correct,byte_erasure,byte_error,weight_errors_erasures,pgf,cascade_bound,
rounded_iid_certificate,historical_iid_certificate,failure_bound,wrong_valid_frame.
Strict local compilation passed; final scoped union audit/commands are recorded in
prometheus-cascaded-fec-265-evidence by integration. Not a new full beta checkpoint.
PhysicalIID, implementation refinement,SKR/WCET and ThirdObligation remain OPEN.
Novelty not-assessed.
