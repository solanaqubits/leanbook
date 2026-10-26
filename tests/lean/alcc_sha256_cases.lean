import Verification.AlgebraicCertificateSHA256
open AlgebraicCertificateSHA256
set_option maxRecDepth 20000
namespace ALCCSHA256Cases

-- cavp_0: shabytetestvectors/SHA256ShortMsg.rsp
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes []) =
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855".toUTF8.toList
    := by decide +kernel
-- cavp_8: shabytetestvectors/SHA256ShortMsg.rsp
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes [211]) =
  "28969cdfa74a12c82f3bad960b0b000aca2ac329deea5c2328ebc6f2ba9802c1".toUTF8.toList
    := by decide +kernel
-- cavp_24: shabytetestvectors/SHA256ShortMsg.rsp
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes [180,25,14]) =
  "dff2e73091f6c05e528896c4c831b9448653dc2ff043528f6769437bc7b975c2".toUTF8.toList
    := by decide +kernel
-- cavp_440: shabytetestvectors/SHA256ShortMsg.rsp
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes [62,191,176,109,184,195,141,91,160,55,241,54,62,17,133,80,170,217,
  70,6,226,104,53,160,26,240,80,120,83,60,194,95,47,57,87,60,4,182,50,246,47,104,194,148,171,49,242,
  163,226,161,160,216,194,190,81]) =
  "6595a2ef537a69ba8583dfbf7f5bec0ab1f93ce4c8ee1916eff44a93af5749c4".toUTF8.toList
    := by decide +kernel
-- cavp_448: shabytetestvectors/SHA256ShortMsg.rsp
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes [45,82,68,125,18,68,210,235,194,134,80,231,176,86,84,186,211,91,58,
  104,238,220,127,133,21,48,107,73,109,117,243,231,51,133,221,27,0,38,37,2,75,129,160,47,47,214,223,
  251,110,109,86,28,183,208,189,122]) =
  "cfb88d6faf2de3a69d36195acec2e255e2af2b7d933997f348e09f6ce5758360".toUTF8.toList
    := by decide +kernel
-- cavp_456: shabytetestvectors/SHA256ShortMsg.rsp
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes [76,172,228,34,228,160,21,167,84,146,179,179,187,251,223,55,88,234,
  255,79,229,4,180,106,38,201,13,172,193,25,250,144,80,246,3,210,181,139,57,140,173,109,109,159,169,
  34,161,84,217,224,188,67,137,150,130,116,176]) =
  "4d54b2d284a6794581224e08f675541c8feab6eefa3ac1cfe5da4e03e62f72e4".toUTF8.toList
    := by decide +kernel
-- cavp_512: shabytetestvectors/SHA256ShortMsg.rsp
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes [90,134,183,55,234,234,142,233,118,160,162,77,166,62,126,215,238,
  250,209,138,16,28,18,17,226,179,101,12,81,135,194,168,166,80,84,114,8,37,31,109,66,55,230,97,199,
  191,76,119,243,53,57,3,148,195,127,161,169,249,190,131,106,194,133,9]) =
  "42e61e174fbb3897d6dd6cef3dd2802fe67b331953b06114a65c772859dfc1aa".toUTF8.toList
    := by decide +kernel
-- abc: NIST SHA256.pdf one block
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes [97,98,99]) =
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad".toUTF8.toList
    := by decide +kernel
-- abc_multiblock: NIST SHA256.pdf two blocks
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes [97,98,99,100,98,99,100,101,99,100,101,102,100,101,102,103,101,102,
  103,104,102,103,104,105,103,104,105,106,104,105,106,107,105,106,107,108,106,107,108,109,107,108,
  109,110,108,109,110,111,109,110,111,112,110,111,112,113]) =
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1".toUTF8.toList
    := by decide +kernel
-- zeros1000: NIST SHA2_Additional.pdf SHA256 #7
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower (SHA256Bytes [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]) =
  "541b3e9daa09b20bf85fa273e5cbd3e80185aa4ec298e765db87742b70138a53".toUTF8.toList
    := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : roundConstants.length = 64 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : hexLower [0, 15, 16, 127, 128, 255] = "000f107f80ff".toUTF8.toList := by
  decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : (pad "abc".toUTF8.toList).take 4 = [97, 98, 99, 128] := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : (pad "abc".toUTF8.toList).drop 56 = [0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : (blockWords (pad "abc".toUTF8.toList))[0]! = 0x61626380 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : (schedule (pad "abc".toUTF8.toList))[16]! = 0x61626380 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.
example : round roundConstants[0]! 0x61626380 initial =
  ⟨0x5d6aebcd, 0x6a09e667, 0xbb67ae85, 0x3c6ef372,
   0xfa2a4622, 0x510e527f, 0x9b05688c, 0x1f83d9ab⟩ := by decide +kernel
#print axioms sha256_refines
#print axioms padded_length_aligned
#print axioms hexLower_valid
end ALCCSHA256Cases
