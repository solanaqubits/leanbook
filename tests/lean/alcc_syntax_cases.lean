import Verification.AlgebraicCertificateSyntax
open AlgebraicCertificateSyntax
namespace ALCCSyntaxCases
def bytes (s : String) : Bytes := s.toUTF8.toList

def positive0 : JsonAST := .array []
example : IsCanonicalAST positive0 := by decide +kernel
example : WithinResourceLimits positive0 := by decide +kernel
example : serializeCanonical positive0 = [91,93] := by rfl
example : parseCanonical [91,93] = some positive0 := by rfl

def positive1 : JsonAST := .object []
example : IsCanonicalAST positive1 := by decide +kernel
example : WithinResourceLimits positive1 := by decide +kernel
example : serializeCanonical positive1 = [123,125] := by rfl
example : parseCanonical [123,125] = some positive1 := by rfl

def positive2 : JsonAST := .number [48]
example : IsCanonicalAST positive2 := by decide +kernel
example : WithinResourceLimits positive2 := by decide +kernel
example : serializeCanonical positive2 = [48] := by rfl
example : parseCanonical [48] = some positive2 := by rfl

def positive3 : JsonAST := .number [52,50]
example : IsCanonicalAST positive3 := by decide +kernel
example : WithinResourceLimits positive3 := by decide +kernel
example : serializeCanonical positive3 = [52,50] := by rfl
example : parseCanonical [52,50] = some positive3 := by rfl

def positive4 : JsonAST := .number [45,49,55]
example : IsCanonicalAST positive4 := by decide +kernel
example : WithinResourceLimits positive4 := by decide +kernel
example : serializeCanonical positive4 = [45,49,55] := by rfl
example : parseCanonical [45,49,55] = some positive4 := by rfl

def positive5 : JsonAST := .null
example : IsCanonicalAST positive5 := by decide +kernel
example : WithinResourceLimits positive5 := by decide +kernel
example : serializeCanonical positive5 = [110,117,108,108] := by rfl
example : parseCanonical [110,117,108,108] = some positive5 := by rfl

def positive6 : JsonAST := .boolean true
example : IsCanonicalAST positive6 := by decide +kernel
example : WithinResourceLimits positive6 := by decide +kernel
example : serializeCanonical positive6 = [116,114,117,101] := by rfl
example : parseCanonical [116,114,117,101] = some positive6 := by rfl

def positive7 : JsonAST := .boolean false
example : IsCanonicalAST positive7 := by decide +kernel
example : WithinResourceLimits positive7 := by decide +kernel
example : serializeCanonical positive7 = [102,97,108,115,101] := by rfl
example : parseCanonical [102,97,108,115,101] = some positive7 := by rfl

def positive8 : JsonAST := .string []
example : IsCanonicalAST positive8 := by decide +kernel
example : WithinResourceLimits positive8 := by decide +kernel
example : serializeCanonical positive8 = [34,34] := by rfl
example : parseCanonical [34,34] = some positive8 := by rfl

def positive9 : JsonAST := .string [97,32,98]
example : IsCanonicalAST positive9 := by decide +kernel
example : WithinResourceLimits positive9 := by decide +kernel
example : serializeCanonical positive9 = [34,97,32,98,34] := by rfl
example : parseCanonical [34,97,32,98,34] = some positive9 := by rfl

def positive10 : JsonAST := .object [([97], .array [.number [48], .number [45,49,55]]), ([98],
  .string [120,32,121,10,127])]
example : IsCanonicalAST positive10 := by decide +kernel
example : WithinResourceLimits positive10 := by decide +kernel
example : serializeCanonical positive10 = [123,34,97,34,58,91,48,44,45,49,55,93,44,34,98,34,58,34,
  120,32,121,92,110,92,117,48,48,55,102,34,125] := by rfl
example : parseCanonical [123,34,97,34,58,91,48,44,45,49,55,93,44,34,98,34,58,34,120,32,121,92,110,
  92,117,48,48,55,102,34,125] = some positive10 := by rfl

-- Negative syntax case 0: b''
example : parseCanonical [] = none := by rfl
-- Negative syntax case 1: b' []'
example : parseCanonical [32,91,93] = none := by rfl
-- Negative syntax case 2: b'[]\n'
example : parseCanonical [91,93,10] = none := by rfl
-- Negative syntax case 3: b'[ ]'
example : parseCanonical [91,32,93] = none := by rfl
-- Negative syntax case 4: b'[0,]'
example : parseCanonical [91,48,44,93] = none := by rfl
-- Negative syntax case 5: b'{"a":0,}'
example : parseCanonical [123,34,97,34,58,48,44,125] = none := by rfl
-- Negative syntax case 6: b'{"b":0,"a":1}'
example : parseCanonical [123,34,98,34,58,48,44,34,97,34,58,49,125] = none := by rfl
-- Negative syntax case 7: b'{"a":0,"a":1}'
example : parseCanonical [123,34,97,34,58,48,44,34,97,34,58,49,125] = none := by rfl
-- Negative syntax case 8: b'1.0'
example : parseCanonical [49,46,48] = none := by rfl
-- Negative syntax case 9: b'1e0'
example : parseCanonical [49,101,48] = none := by rfl
-- Negative syntax case 10: b'01'
example : parseCanonical [48,49] = none := by rfl
-- Negative syntax case 11: b'-0'
example : parseCanonical [45,48] = none := by rfl
-- Negative syntax case 12: b'+1'
example : parseCanonical [43,49] = none := by rfl
-- Negative syntax case 13: b'--1'
example : parseCanonical [45,45,49] = none := by rfl
-- Negative syntax case 14: b'NaN'
example : parseCanonical [78,97,78] = none := by rfl
-- Negative syntax case 15: b'Infinity'
example : parseCanonical [73,110,102,105,110,105,116,121] = none := by rfl
-- Negative syntax case 16: b'"\\u0061"'
example : parseCanonical [34,92,117,48,48,54,49,34] = none := by rfl
-- Negative syntax case 17: b'"\\/"'
example : parseCanonical [34,92,47,34] = none := by rfl
-- Negative syntax case 18: b'"\\u007F"'
example : parseCanonical [34,92,117,48,48,55,70,34] = none := by rfl
-- Negative syntax case 19: b'"\x7f"'
example : parseCanonical [34,127,34] = none := by rfl
-- Negative syntax case 20: b'"\n"'
example : parseCanonical [34,10,34] = none := by rfl
-- Negative syntax case 21: b'"\\u0008"'
example : parseCanonical [34,92,117,48,48,48,56,34] = none := by rfl
-- Negative syntax case 22: b'"\\u0080"'
example : parseCanonical [34,92,117,48,48,56,48,34] = none := by rfl
-- Negative syntax case 23: b'"\x80"'
example : parseCanonical [34,128,34] = none := by rfl
-- Negative syntax case 24: b'\xef\xbb\xbf[]'
example : parseCanonical [239,187,191,91,93] = none := by rfl
-- Negative syntax case 25: b'[]{}'
example : parseCanonical [91,93,123,125] = none := by rfl
-- Negative syntax case 26: b'{a:0}'
example : parseCanonical [123,97,58,48,125] = none := by rfl
-- Negative syntax case 27: b'"unterminated'
example : parseCanonical [34,117,110,116,101,114,109,105,110,97,116,101,100] = none := by rfl
-- Negative syntax case 28: b'['
example : parseCanonical [91] = none := by rfl
-- Negative syntax case 29: b'{'
example : parseCanonical [123] = none := by rfl
-- Negative syntax case 30: b'"\\q"'
example : parseCanonical [34,92,113,34] = none := by rfl
example : serializeString [0] = [34,92,117,48,48,48,48,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,48,34] = some (.string [0]) := by rfl
example : serializeString [1] = [34,92,117,48,48,48,49,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,49,34] = some (.string [1]) := by rfl
example : serializeString [2] = [34,92,117,48,48,48,50,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,50,34] = some (.string [2]) := by rfl
example : serializeString [3] = [34,92,117,48,48,48,51,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,51,34] = some (.string [3]) := by rfl
example : serializeString [4] = [34,92,117,48,48,48,52,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,52,34] = some (.string [4]) := by rfl
example : serializeString [5] = [34,92,117,48,48,48,53,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,53,34] = some (.string [5]) := by rfl
example : serializeString [6] = [34,92,117,48,48,48,54,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,54,34] = some (.string [6]) := by rfl
example : serializeString [7] = [34,92,117,48,48,48,55,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,55,34] = some (.string [7]) := by rfl
example : serializeString [8] = [34,92,98,34] := by rfl
example : parseCanonical [34,92,98,34] = some (.string [8]) := by rfl
example : serializeString [9] = [34,92,116,34] := by rfl
example : parseCanonical [34,92,116,34] = some (.string [9]) := by rfl
example : serializeString [10] = [34,92,110,34] := by rfl
example : parseCanonical [34,92,110,34] = some (.string [10]) := by rfl
example : serializeString [11] = [34,92,117,48,48,48,98,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,98,34] = some (.string [11]) := by rfl
example : serializeString [12] = [34,92,102,34] := by rfl
example : parseCanonical [34,92,102,34] = some (.string [12]) := by rfl
example : serializeString [13] = [34,92,114,34] := by rfl
example : parseCanonical [34,92,114,34] = some (.string [13]) := by rfl
example : serializeString [14] = [34,92,117,48,48,48,101,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,101,34] = some (.string [14]) := by rfl
example : serializeString [15] = [34,92,117,48,48,48,102,34] := by rfl
example : parseCanonical [34,92,117,48,48,48,102,34] = some (.string [15]) := by rfl
example : serializeString [16] = [34,92,117,48,48,49,48,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,48,34] = some (.string [16]) := by rfl
example : serializeString [17] = [34,92,117,48,48,49,49,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,49,34] = some (.string [17]) := by rfl
example : serializeString [18] = [34,92,117,48,48,49,50,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,50,34] = some (.string [18]) := by rfl
example : serializeString [19] = [34,92,117,48,48,49,51,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,51,34] = some (.string [19]) := by rfl
example : serializeString [20] = [34,92,117,48,48,49,52,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,52,34] = some (.string [20]) := by rfl
example : serializeString [21] = [34,92,117,48,48,49,53,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,53,34] = some (.string [21]) := by rfl
example : serializeString [22] = [34,92,117,48,48,49,54,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,54,34] = some (.string [22]) := by rfl
example : serializeString [23] = [34,92,117,48,48,49,55,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,55,34] = some (.string [23]) := by rfl
example : serializeString [24] = [34,92,117,48,48,49,56,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,56,34] = some (.string [24]) := by rfl
example : serializeString [25] = [34,92,117,48,48,49,57,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,57,34] = some (.string [25]) := by rfl
example : serializeString [26] = [34,92,117,48,48,49,97,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,97,34] = some (.string [26]) := by rfl
example : serializeString [27] = [34,92,117,48,48,49,98,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,98,34] = some (.string [27]) := by rfl
example : serializeString [28] = [34,92,117,48,48,49,99,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,99,34] = some (.string [28]) := by rfl
example : serializeString [29] = [34,92,117,48,48,49,100,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,100,34] = some (.string [29]) := by rfl
example : serializeString [30] = [34,92,117,48,48,49,101,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,101,34] = some (.string [30]) := by rfl
example : serializeString [31] = [34,92,117,48,48,49,102,34] := by rfl
example : parseCanonical [34,92,117,48,48,49,102,34] = some (.string [31]) := by rfl
example : serializeString [32] = [34,32,34] := by rfl
example : parseCanonical [34,32,34] = some (.string [32]) := by rfl
example : serializeString [33] = [34,33,34] := by rfl
example : parseCanonical [34,33,34] = some (.string [33]) := by rfl
example : serializeString [34] = [34,92,34,34] := by rfl
example : parseCanonical [34,92,34,34] = some (.string [34]) := by rfl
example : serializeString [35] = [34,35,34] := by rfl
example : parseCanonical [34,35,34] = some (.string [35]) := by rfl
example : serializeString [36] = [34,36,34] := by rfl
example : parseCanonical [34,36,34] = some (.string [36]) := by rfl
example : serializeString [37] = [34,37,34] := by rfl
example : parseCanonical [34,37,34] = some (.string [37]) := by rfl
example : serializeString [38] = [34,38,34] := by rfl
example : parseCanonical [34,38,34] = some (.string [38]) := by rfl
example : serializeString [39] = [34,39,34] := by rfl
example : parseCanonical [34,39,34] = some (.string [39]) := by rfl
example : serializeString [40] = [34,40,34] := by rfl
example : parseCanonical [34,40,34] = some (.string [40]) := by rfl
example : serializeString [41] = [34,41,34] := by rfl
example : parseCanonical [34,41,34] = some (.string [41]) := by rfl
example : serializeString [42] = [34,42,34] := by rfl
example : parseCanonical [34,42,34] = some (.string [42]) := by rfl
example : serializeString [43] = [34,43,34] := by rfl
example : parseCanonical [34,43,34] = some (.string [43]) := by rfl
example : serializeString [44] = [34,44,34] := by rfl
example : parseCanonical [34,44,34] = some (.string [44]) := by rfl
example : serializeString [45] = [34,45,34] := by rfl
example : parseCanonical [34,45,34] = some (.string [45]) := by rfl
example : serializeString [46] = [34,46,34] := by rfl
example : parseCanonical [34,46,34] = some (.string [46]) := by rfl
example : serializeString [47] = [34,47,34] := by rfl
example : parseCanonical [34,47,34] = some (.string [47]) := by rfl
example : serializeString [48] = [34,48,34] := by rfl
example : parseCanonical [34,48,34] = some (.string [48]) := by rfl
example : serializeString [49] = [34,49,34] := by rfl
example : parseCanonical [34,49,34] = some (.string [49]) := by rfl
example : serializeString [50] = [34,50,34] := by rfl
example : parseCanonical [34,50,34] = some (.string [50]) := by rfl
example : serializeString [51] = [34,51,34] := by rfl
example : parseCanonical [34,51,34] = some (.string [51]) := by rfl
example : serializeString [52] = [34,52,34] := by rfl
example : parseCanonical [34,52,34] = some (.string [52]) := by rfl
example : serializeString [53] = [34,53,34] := by rfl
example : parseCanonical [34,53,34] = some (.string [53]) := by rfl
example : serializeString [54] = [34,54,34] := by rfl
example : parseCanonical [34,54,34] = some (.string [54]) := by rfl
example : serializeString [55] = [34,55,34] := by rfl
example : parseCanonical [34,55,34] = some (.string [55]) := by rfl
example : serializeString [56] = [34,56,34] := by rfl
example : parseCanonical [34,56,34] = some (.string [56]) := by rfl
example : serializeString [57] = [34,57,34] := by rfl
example : parseCanonical [34,57,34] = some (.string [57]) := by rfl
example : serializeString [58] = [34,58,34] := by rfl
example : parseCanonical [34,58,34] = some (.string [58]) := by rfl
example : serializeString [59] = [34,59,34] := by rfl
example : parseCanonical [34,59,34] = some (.string [59]) := by rfl
example : serializeString [60] = [34,60,34] := by rfl
example : parseCanonical [34,60,34] = some (.string [60]) := by rfl
example : serializeString [61] = [34,61,34] := by rfl
example : parseCanonical [34,61,34] = some (.string [61]) := by rfl
example : serializeString [62] = [34,62,34] := by rfl
example : parseCanonical [34,62,34] = some (.string [62]) := by rfl
example : serializeString [63] = [34,63,34] := by rfl
example : parseCanonical [34,63,34] = some (.string [63]) := by rfl
example : serializeString [64] = [34,64,34] := by rfl
example : parseCanonical [34,64,34] = some (.string [64]) := by rfl
example : serializeString [65] = [34,65,34] := by rfl
example : parseCanonical [34,65,34] = some (.string [65]) := by rfl
example : serializeString [66] = [34,66,34] := by rfl
example : parseCanonical [34,66,34] = some (.string [66]) := by rfl
example : serializeString [67] = [34,67,34] := by rfl
example : parseCanonical [34,67,34] = some (.string [67]) := by rfl
example : serializeString [68] = [34,68,34] := by rfl
example : parseCanonical [34,68,34] = some (.string [68]) := by rfl
example : serializeString [69] = [34,69,34] := by rfl
example : parseCanonical [34,69,34] = some (.string [69]) := by rfl
example : serializeString [70] = [34,70,34] := by rfl
example : parseCanonical [34,70,34] = some (.string [70]) := by rfl
example : serializeString [71] = [34,71,34] := by rfl
example : parseCanonical [34,71,34] = some (.string [71]) := by rfl
example : serializeString [72] = [34,72,34] := by rfl
example : parseCanonical [34,72,34] = some (.string [72]) := by rfl
example : serializeString [73] = [34,73,34] := by rfl
example : parseCanonical [34,73,34] = some (.string [73]) := by rfl
example : serializeString [74] = [34,74,34] := by rfl
example : parseCanonical [34,74,34] = some (.string [74]) := by rfl
example : serializeString [75] = [34,75,34] := by rfl
example : parseCanonical [34,75,34] = some (.string [75]) := by rfl
example : serializeString [76] = [34,76,34] := by rfl
example : parseCanonical [34,76,34] = some (.string [76]) := by rfl
example : serializeString [77] = [34,77,34] := by rfl
example : parseCanonical [34,77,34] = some (.string [77]) := by rfl
example : serializeString [78] = [34,78,34] := by rfl
example : parseCanonical [34,78,34] = some (.string [78]) := by rfl
example : serializeString [79] = [34,79,34] := by rfl
example : parseCanonical [34,79,34] = some (.string [79]) := by rfl
example : serializeString [80] = [34,80,34] := by rfl
example : parseCanonical [34,80,34] = some (.string [80]) := by rfl
example : serializeString [81] = [34,81,34] := by rfl
example : parseCanonical [34,81,34] = some (.string [81]) := by rfl
example : serializeString [82] = [34,82,34] := by rfl
example : parseCanonical [34,82,34] = some (.string [82]) := by rfl
example : serializeString [83] = [34,83,34] := by rfl
example : parseCanonical [34,83,34] = some (.string [83]) := by rfl
example : serializeString [84] = [34,84,34] := by rfl
example : parseCanonical [34,84,34] = some (.string [84]) := by rfl
example : serializeString [85] = [34,85,34] := by rfl
example : parseCanonical [34,85,34] = some (.string [85]) := by rfl
example : serializeString [86] = [34,86,34] := by rfl
example : parseCanonical [34,86,34] = some (.string [86]) := by rfl
example : serializeString [87] = [34,87,34] := by rfl
example : parseCanonical [34,87,34] = some (.string [87]) := by rfl
example : serializeString [88] = [34,88,34] := by rfl
example : parseCanonical [34,88,34] = some (.string [88]) := by rfl
example : serializeString [89] = [34,89,34] := by rfl
example : parseCanonical [34,89,34] = some (.string [89]) := by rfl
example : serializeString [90] = [34,90,34] := by rfl
example : parseCanonical [34,90,34] = some (.string [90]) := by rfl
example : serializeString [91] = [34,91,34] := by rfl
example : parseCanonical [34,91,34] = some (.string [91]) := by rfl
example : serializeString [92] = [34,92,92,34] := by rfl
example : parseCanonical [34,92,92,34] = some (.string [92]) := by rfl
example : serializeString [93] = [34,93,34] := by rfl
example : parseCanonical [34,93,34] = some (.string [93]) := by rfl
example : serializeString [94] = [34,94,34] := by rfl
example : parseCanonical [34,94,34] = some (.string [94]) := by rfl
example : serializeString [95] = [34,95,34] := by rfl
example : parseCanonical [34,95,34] = some (.string [95]) := by rfl
example : serializeString [96] = [34,96,34] := by rfl
example : parseCanonical [34,96,34] = some (.string [96]) := by rfl
example : serializeString [97] = [34,97,34] := by rfl
example : parseCanonical [34,97,34] = some (.string [97]) := by rfl
example : serializeString [98] = [34,98,34] := by rfl
example : parseCanonical [34,98,34] = some (.string [98]) := by rfl
example : serializeString [99] = [34,99,34] := by rfl
example : parseCanonical [34,99,34] = some (.string [99]) := by rfl
example : serializeString [100] = [34,100,34] := by rfl
example : parseCanonical [34,100,34] = some (.string [100]) := by rfl
example : serializeString [101] = [34,101,34] := by rfl
example : parseCanonical [34,101,34] = some (.string [101]) := by rfl
example : serializeString [102] = [34,102,34] := by rfl
example : parseCanonical [34,102,34] = some (.string [102]) := by rfl
example : serializeString [103] = [34,103,34] := by rfl
example : parseCanonical [34,103,34] = some (.string [103]) := by rfl
example : serializeString [104] = [34,104,34] := by rfl
example : parseCanonical [34,104,34] = some (.string [104]) := by rfl
example : serializeString [105] = [34,105,34] := by rfl
example : parseCanonical [34,105,34] = some (.string [105]) := by rfl
example : serializeString [106] = [34,106,34] := by rfl
example : parseCanonical [34,106,34] = some (.string [106]) := by rfl
example : serializeString [107] = [34,107,34] := by rfl
example : parseCanonical [34,107,34] = some (.string [107]) := by rfl
example : serializeString [108] = [34,108,34] := by rfl
example : parseCanonical [34,108,34] = some (.string [108]) := by rfl
example : serializeString [109] = [34,109,34] := by rfl
example : parseCanonical [34,109,34] = some (.string [109]) := by rfl
example : serializeString [110] = [34,110,34] := by rfl
example : parseCanonical [34,110,34] = some (.string [110]) := by rfl
example : serializeString [111] = [34,111,34] := by rfl
example : parseCanonical [34,111,34] = some (.string [111]) := by rfl
example : serializeString [112] = [34,112,34] := by rfl
example : parseCanonical [34,112,34] = some (.string [112]) := by rfl
example : serializeString [113] = [34,113,34] := by rfl
example : parseCanonical [34,113,34] = some (.string [113]) := by rfl
example : serializeString [114] = [34,114,34] := by rfl
example : parseCanonical [34,114,34] = some (.string [114]) := by rfl
example : serializeString [115] = [34,115,34] := by rfl
example : parseCanonical [34,115,34] = some (.string [115]) := by rfl
example : serializeString [116] = [34,116,34] := by rfl
example : parseCanonical [34,116,34] = some (.string [116]) := by rfl
example : serializeString [117] = [34,117,34] := by rfl
example : parseCanonical [34,117,34] = some (.string [117]) := by rfl
example : serializeString [118] = [34,118,34] := by rfl
example : parseCanonical [34,118,34] = some (.string [118]) := by rfl
example : serializeString [119] = [34,119,34] := by rfl
example : parseCanonical [34,119,34] = some (.string [119]) := by rfl
example : serializeString [120] = [34,120,34] := by rfl
example : parseCanonical [34,120,34] = some (.string [120]) := by rfl
example : serializeString [121] = [34,121,34] := by rfl
example : parseCanonical [34,121,34] = some (.string [121]) := by rfl
example : serializeString [122] = [34,122,34] := by rfl
example : parseCanonical [34,122,34] = some (.string [122]) := by rfl
example : serializeString [123] = [34,123,34] := by rfl
example : parseCanonical [34,123,34] = some (.string [123]) := by rfl
example : serializeString [124] = [34,124,34] := by rfl
example : parseCanonical [34,124,34] = some (.string [124]) := by rfl
example : serializeString [125] = [34,125,34] := by rfl
example : parseCanonical [34,125,34] = some (.string [125]) := by rfl
example : serializeString [126] = [34,126,34] := by rfl
example : parseCanonical [34,126,34] = some (.string [126]) := by rfl
example : serializeString [127] = [34,92,117,48,48,55,102,34] := by rfl
example : parseCanonical [34,92,117,48,48,55,102,34] = some (.string [127]) := by rfl
def nest : Nat → JsonAST
  | 0 => .number [48]
  | n+1 => .array [nest n]
example : IsCanonicalAST (nest 17) := by decide +kernel
example : ¬ WithinResourceLimits (nest 17) := by decide +kernel
example : parseCanonical (serializeCanonical (nest 17)) = none := by rfl
example : parseCanonical (serializeCanonical (nest 16)) = some (nest 16) := by rfl
example (t : JsonAST) (hc : IsCanonicalAST t) (hr : WithinResourceLimits t) :
    parseCanonical (serializeCanonical t) = some t := parseCanonical_complete t hc hr
example (b : Bytes) (a c : JsonAST) (ha : CanonicalParseRel b a)
    (hc : CanonicalParseRel b c) : a = c := canonicalParse_deterministic ha hc
end ALCCSyntaxCases
#print axioms AlgebraicCertificateSyntax.parseCanonical_sound
#print axioms AlgebraicCertificateSyntax.canonicalParse_deterministic
#print axioms AlgebraicCertificateSyntax.parseCanonical_complete
#print axioms AlgebraicCertificateSyntax.accepted_ascii
