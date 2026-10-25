---
id: AlgebraicCertificateSHA256
language: en
section: proof-graphs
source: Verification/AlgebraicCertificateSHA256.lean
source_sha256: 863837bd9656b99f0bb54c603168772928116211f23af4c18bd63e4859f1544d
novelty: not-assessed
---

# SHA-256 functional refinement

[Section](README.md) · [Lean source](../../Verification/AlgebraicCertificateSHA256.lean)

Relates the executable SHA256Bytes function to an explicitly written functional Spec.SHA256Bytes model. The domain requires message length below 2^61 bytes. The model was manually transcribed from FIPS 180-4 and is tested with ten vectors; this is not NIST/CAVP certification or a collision-resistance proof.

## Interfaces and proof scope

- `beBytes`
- `paddingZeros`
- `pad`
- `MessageDomain`
- `blocks`
- `rotr`
- `ch`
- `maj`
- `big0`
- `big1`
- `small0`
- `small1`
- `roundConstants`
- `State`
- `initial`
- `feedForward`
- `round`
- `blockWords`
- `scheduleStep`
- `recurrence`
- `loop`
- `loop_refines`
- `schedule`
- `compress`
- `hashState`
- `schedule`
- `compress`
- `hashState`
- `digest`
- `Spec`
- `SHA256Bytes`
- `schedule_refines`
- `compress_refines`
- `hashState_refines`
- `sha256_refines`
- `digest_length`
- `sha256_length`
- `hexDigit`
- `hexLower`
- `hexLower_length`
- `sha256_hex_length`
- `paddingZeros_lt`
- `padded_length_aligned`
- `schedule_length`
- `paddingZeros_minimal`
- `message_bit_length`
- `lowerHexByte`
- `hexDigit_valid`
- `hexLower_valid`

The source types specify the actual hypotheses. See the [ALCC guide](../../docs/alcc.en.md) for execution and trust boundaries. Scientific priority is not assessed.
