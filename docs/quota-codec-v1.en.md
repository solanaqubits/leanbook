# QuotaCursorSnapshot v1 format (epsilon240)

The magic/version is ASCII QCS followed by byte 01: `51 43 53 01` in hex.
A frame contains magic/version, ULEB128(bound), ULEB128(row.length), then exactly
that many rational entries and EOF. The empty bound-zero snapshot is `51 43 53 01 00 00`.

ULEB128 uses minimal seven-bit groups, least significant first, with the high bit
indicating continuation. A multibyte integer cannot end with a zero payload group;
intermediate zero groups are allowed. Truncated integers are rejected.

Each rational contains a sign byte (00 or 01), ULEB128(abs numerator), and
ULEB128(denominator). The denominator is positive and coprime with the absolute
numerator. Negative zero is rejected; zero has the unique encoding `00 00 01`.
Reducible inputs are rejected rather than normalized. Trailing bytes are rejected.

`Fits limits s` requires bound <= maxBound, row.length <= maxRowLength and the
entire encoded frame size <= maxSizeBytes. Zero size permits no frame; zero bound
and row limits still permit bound zero and an empty row if the size limit permits.

Proved properties:

- `Fits limits s` implies `strictDecode limits (encodeV1 s) = some s`.
- `strictDecode limits bytes = some s` implies `Fits limits s` and `encodeV1 s = bytes`.

The decoder checks input size before parsing, bound before row parsing and count
before constructing row entries. It does not preallocate from an unchecked count.
An exact re-encoding equality check enforces canonical acceptance; a hash does not
replace that equality.

The API receives an existing ByteArray. The separate [reader](quota-snapshot-reader.en.md)
bounds file reads before decoding. Neither layer proves total CPU, memory or time
bounds for recursion, large-integer arithmetic, list conversion and re-encoding.
`strictDecode` has no n, p, j or epsilon context and does not replace `restoreCursor?`.
Format validity and mathematical validity establish neither provenance nor authorization.
