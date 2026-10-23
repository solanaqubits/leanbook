import Init

-- Runtime-only externs: effects remain explicit in IO.
namespace ProvenanceNative
@[extern "provenance_verify_io"]
opaque rawVerify (path version : @& String) (key message signature : @& ByteArray) : IO UInt8
@[extern "provenance_sha256_io"]
opaque rawHash (path version : @& String) (message : @& ByteArray) : IO ByteArray

end ProvenanceNative
