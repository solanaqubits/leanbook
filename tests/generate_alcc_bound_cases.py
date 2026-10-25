"""Independent byte/digest fixtures. Neither hashlib nor json is a proof premise."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from tests.generate_alcc_schema_cases import task, term, nums, ast, view
from tests.generate_alcc_unbound_cases import wire

ROOT = Path(__file__).resolve().parents[1]


def bind(pair):
    p, c = deepcopy(pair)
    body = {k: v for k, v in p.items() if k != 'problem_id'}
    p['problem_id'] = hashlib.sha256(wire(body)).hexdigest()
    c['problem_id'] = p['problem_id']
    return p, c


def generate():
    vectors = json.loads((ROOT/'tests/fixtures/alcc-bound/nist-sha256.json').read_text())['vectors']
    sha = ['''import Verification.AlgebraicCertificateSHA256
open AlgebraicCertificateSHA256
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ALCCSHA256Cases
''']
    for row in vectors:
        sha += [f'-- {row["name"]}: {row["source"]}',
                f'example : hexLower (SHA256Bytes {nums(bytes.fromhex(row["message_hex"]))}) =',
                f'  "{row["digest"]}".toUTF8.toList := by decide +kernel']
    sha += ['''example : roundConstants.length = 64 := by decide +kernel
example : hexLower [0, 15, 16, 127, 128, 255] = "000f107f80ff".toUTF8.toList := by
  decide +kernel
example : (pad "abc".toUTF8.toList).take 4 = [97, 98, 99, 128] := by decide +kernel
example : (pad "abc".toUTF8.toList).drop 56 = [0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel
example : (blockWords (pad "abc".toUTF8.toList))[0]! = 0x61626380 := by decide +kernel
example : (schedule (pad "abc".toUTF8.toList))[16]! = 0x61626380 := by decide +kernel
example : round roundConstants[0]! 0x61626380 initial =
  ⟨0x5d6aebcd, 0x6a09e667, 0xbb67ae85, 0x3c6ef372,
   0xfa2a4622, 0x510e527f, 0x9b05688c, 0x1f83d9ab⟩ := by decide +kernel
#print axioms sha256_refines
#print axioms padded_length_aligned
#print axioms hexLower_valid
end ALCCSHA256Cases
''']
    reference = task(['x', 'y', 'z'],
                     [[term(1, 1, [2, 0, 0]), term(-1, 1, [0, 1, 0])],
                      [term(1, 1, [0, 2, 0]), term(-1, 1, [0, 0, 1])]],
                     [term(1, 1, [4, 0, 0]), term(-1, 1, [0, 0, 1])],
                     [[term(1, 1, [2, 0, 0]), term(1, 1, [0, 1, 0])],
                      [term(1, 1, [0, 0, 0])]])
    invalid = deepcopy(reference)
    invalid[1]['multipliers'][0]['poly'].append(term(1, 1, [0, 0, 0]))
    positive = [('empty', bind(task([], [], [], []))), ('reference', bind(reference)),
                ('fraction', bind(task(['z', 'a'], [[term(-1, 2, [0, 1])]],
                                      [term(3, 4, [0, 1])], [[term(-3, 2, [0, 0])]]))),
                ('invalid_identity', bind(invalid))]
    negative = []
    def bad(name, edit):
        p, c = deepcopy(positive[1][1]); edit(p, c); negative.append((name, p, c))
    bad('foreign_certificate', lambda p, c: c.update(problem_id='f'*64))
    bad('forged_pair', lambda p, c: (p.update(problem_id='0'*64), c.update(problem_id='0'*64)))
    bad('mutated_target', lambda p, c: p['target']['poly'][0].update(coeff=[2, 1]))
    bad('changed_variables', lambda p, c: p.update(variables=['a', 'y', 'z']))
    bad('uppercase_digest', lambda p, c: c.update(problem_id=c['problem_id'].upper()))
    bad('short_digest', lambda p, c: c.update(problem_id=c['problem_id'][:-1]))
    bad('missing_digest', lambda p, c: p.pop('problem_id'))
    bad('wrong_profile', lambda p, c: p.update(profile_id='ALCC-JSON-2'))
    body = {k:v for k,v in positive[1][1][0].items() if k != 'problem_id'}
    wrong = hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest()
    bad('noncanonical_hash_preimage', lambda p,c: (p.update(problem_id=wrong),c.update(problem_id=wrong)))
    full = hashlib.sha256(wire(positive[1][1][0])).hexdigest()
    bad('included_problem_id', lambda p,c: (p.update(problem_id=full),c.update(problem_id=full)))
    lines = ['''import Verification.AlgebraicCertificateBound
open AlgebraicCertificateSyntax AlgebraicCertificateSchema AlgebraicCertificateKernel
open AlgebraicCertificateUnbound AlgebraicCertificateBound
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ALCCBoundCases
abbrev PolyView := List (List ℕ × ℚ)
def pv {n : ℕ} (p : SparsePoly n) : PolyView := p.map (fun t => (t.1.val, t.2))
structure TaskView where
  n : ℕ
  m : ℕ
  target : PolyView
  hypotheses : List PolyView
  multipliers : List PolyView
  deriving DecidableEq

def taskView (t : UnboundTask) : TaskView :=
  ⟨t.1, t.2.1, pv t.2.2.1.target, List.ofFn (fun i => pv (t.2.2.1.hypotheses i)),
    List.ofFn (fun i => pv (t.2.2.2.multipliers i))⟩
''']
    for name, (p,c) in positive:
        lines += [f'def p_{name} : Bytes := {nums(wire(p))}',
                  f'def c_{name} : Bytes := {nums(wire(c))}',
                  f'example : (decodeBoundTask p_{name} c_{name}).map taskView = some {view(p,c)} := by decide +kernel',
                  f'theorem accepted_{name} : (decodeBoundTask p_{name} c_{name}).isSome = true := by decide +kernel',
                  f'example : ∃ t, BoundTaskRel p_{name} c_{name} t := AlgebraicCertificateBound.accepted_has_relation accepted_{name}']
    for name,p,c in negative:
        lines += [f'-- Rejection: {name}', f'def p_{name} : Bytes := {nums(wire(p))}',
                  f'def c_{name} : Bytes := {nums(wire(c))}',
                  f'example : (decodeBoundTask p_{name} c_{name}).isNone = true := by decide +kernel']
        if name in ['foreign_certificate','forged_pair','mutated_target','changed_variables',
                    'noncanonical_hash_preimage','included_problem_id']:
            lines += [f'example : (decodeFromBytes p_{name} c_{name}).isSome = true := by decide +kernel']
    lines += ['''example : (decodeBoundTask (32 :: p_reference) c_reference).isNone = true := by
  decide +kernel
example : (decodeBoundTask p_reference (c_reference ++ [10])).isNone = true := by
  decide +kernel
example : (decodeBoundTask p_reference c_reference).map
    (fun t => checkCert t.2.2.1 t.2.2.2) = some true := by decide +kernel
example : (decodeBoundTask p_invalid_identity c_invalid_identity).map
    (fun t => checkCert t.2.2.1 t.2.2.2) = some false := by decide +kernel
example : bindingCheck (.object []) (.object []) = false := by decide +kernel
''', f'example : passportBody {ast(positive[1][1][0])} = {nums(wire(body))} := by decide +kernel',
              '''example {bp bc : Bytes} {a b : UnboundTask}
    (ha : BoundTaskRel bp bc a) (hb : BoundTaskRel bp bc b) : a = b :=
  boundTaskRel_deterministic ha hb
#print axioms decodeBoundTask_sound
#print axioms boundTaskRel_deterministic
#print axioms removeProblemId_canonical
end ALCCBoundCases
''']
    sources = {'sha256': '\n'.join(sha), 'bound': '\n'.join(lines)}
    meta = {'nist_vectors':len(vectors),'positive_pairs':len(positive),'negative_pairs':len(negative)+2,
            'sha_assertions':len(vectors)+7,'bound_assertions':len(positive)*3+len(negative)+6+7}
    return sources, meta


if __name__ == '__main__':
    sources, metadata = generate()
    for name, source in sources.items():
        (ROOT/f'tests/lean/alcc_{name}_cases.lean').write_text(source)
    print(metadata)
