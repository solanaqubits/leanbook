"""Explicit byte fixtures for the Lean composition, prepared with stdlib JSON.

The proof checks actual byte lists; no Lean serializer constructs these inputs.
This finite fixture preparation is not a proof of Python's JSON implementation.
"""
from tools.lean_fixture_format import wrap_source
from copy import deepcopy
import json
from pathlib import Path
from tests.generate_alcc_schema_cases import task, term, nums, view

ROOT = Path(__file__).resolve().parents[1]


def wire(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode('ascii')


def generate():
    reference = task(['x', 'y', 'z'],
                     [[term(1, 1, [2, 0, 0]), term(-1, 1, [0, 1, 0])],
                      [term(1, 1, [0, 2, 0]), term(-1, 1, [0, 0, 1])]],
                     [term(1, 1, [4, 0, 0]), term(-1, 1, [0, 0, 1])],
                     [[term(1, 1, [2, 0, 0]), term(1, 1, [0, 1, 0])],
                      [term(1, 1, [0, 0, 0])]])
    positive = [('empty', task([], [], [], [])), ('reference', reference),
                ('fraction', task(['x'], [[term(-1, 2, [1])]],
                                  [term(3, 4, [1])], [[term(-3, 2, [0])]])),
                ('positions', task(['z', 'a'], [[term(1, 1, [0, 1])]],
                                   [term(1, 1, [0, 1])], [[term(1, 1, [0, 0])]]))]
    unbound = deepcopy(reference); unbound[1]['problem_id'] = 'f' * 64
    positive.append(('different_digests', unbound))
    invalid = deepcopy(reference)
    invalid[1]['multipliers'][0]['poly'].append(term(1, 1, [0, 0, 0]))
    positive.append(('invalid_identity', invalid))
    syntax = []
    for side in range(2):
        good = wire(reference[side])
        variants = [('leading_space', b' ' + good), ('trailing_newline', good + b'\n'),
                    ('raw_control', good.replace(b'"h0"', b'"h\n"', 1)),
                    ('float_token', good.replace(b'"coeff":[1,1]', b'"coeff":[1.0,1]', 1)),
                    ('nonascii', good.replace(b'"h0"', b'"\x80"', 1)),
                    ('unordered_keys', json.dumps(dict(reversed(sorted(reference[side].items()))),
                                                  separators=(',', ':')).encode('ascii')),
                    ('duplicate_key', b'{"format_version":"1.0",' + good[1:]),
                    ('redundant_escape', good.replace(b'"h0"', b'"\\u00680"', 1))]
        for name, bad in variants:
            assert bad != good
            pair = [wire(x) for x in reference]; pair[side] = bad
            syntax.append((f'{name}_{side}', side, pair))
    structural = []

    def bad(name, f):
        pair = deepcopy(reference); f(*pair); structural.append((name, pair))

    bad('reducible', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=[2, 4]))
    bad('zero_numerator', lambda p, c: p['target']['poly'][0].update(coeff=[0, 1]))
    bad('wrong_id', lambda p, c: c['multipliers'][0].update(hypothesis_id='h1'))
    bad('duplicate_variables', lambda p, c: p.update(variables=['x', 'x', 'z']))
    bad('missing_multiplier', lambda p, c: c['multipliers'].pop())
    bad('reversed_terms', lambda p, c: c['multipliers'][0]['poly'].reverse())
    bad('extra_field', lambda p, c: p.update(extra=0))
    lines = ['''import Verification.AlgebraicCertificateUnbound
open AlgebraicCertificateSyntax AlgebraicCertificateSchema AlgebraicCertificateKernel
open AlgebraicCertificateUnbound
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ALCCUnboundCases
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
    for name, (p, c) in positive:
        lines += [f'def p_{name} : Bytes := {nums(wire(p))}',
                  f'def c_{name} : Bytes := {nums(wire(c))}',
                  f'example : (decodeFromBytes p_{name} c_{name}).map taskView = some {view(p,c)} := by decide +kernel',
                  f'theorem accepted_{name} : (decodeFromBytes p_{name} c_{name}).isSome = true := by decide +kernel',
                  f'example : ∃ t, UnboundTaskRel p_{name} c_{name} t := accepted_has_relation accepted_{name}']
    for name, side, (p, c) in syntax:
        lines += [f'-- Syntactic refusal: {name}',
                  f'def p_{name} : Bytes := {nums(p)}', f'def c_{name} : Bytes := {nums(c)}',
                  f'example : (parseCanonical {"p" if side == 0 else "c"}_{name}).isNone = true := by decide +kernel',
                  f'example : (decodeFromBytes p_{name} c_{name}).isNone = true := by decide +kernel']
    for name, (p, c) in structural:
        lines += [f'-- Canonical syntax, rejected schema: {name}',
                  f'def p_{name} : Bytes := {nums(wire(p))}', f'def c_{name} : Bytes := {nums(wire(c))}',
                  f'example : (parseCanonical p_{name}).isSome = true := by decide +kernel',
                  f'example : (parseCanonical c_{name}).isSome = true := by decide +kernel',
                  f'example : (decodeFromBytes p_{name} c_{name}).isNone = true := by decide +kernel']
    lines += ['''example : (decodeFromBytes p_reference c_reference).map
    (fun t => checkCert t.2.2.1 t.2.2.2) = some true := by decide +kernel
example : (decodeFromBytes p_invalid_identity c_invalid_identity).map
    (fun t => checkCert t.2.2.1 t.2.2.2) = some false := by decide +kernel
example {bp bc : Bytes} {a b : UnboundTask}
    (ha : UnboundTaskRel bp bc a) (hb : UnboundTaskRel bp bc b) : a = b :=
  unboundTaskRel_deterministic ha hb
#print axioms decodeFromBytes_sound
#print axioms unboundTaskRel_deterministic
#print axioms decodeFromBytes_serialized
end ALCCUnboundCases
''']
    metadata = dict(positive_pairs=len(positive),syntax_refusals=len(syntax),
                    schema_refusals=len(structural),lean_assertions=len(positive)*3+len(syntax)*2+len(structural)*3+3)
    return wrap_source('\n'.join(lines)), metadata


if __name__ == '__main__':
    source, metadata = generate()
    (ROOT/'tests/lean/alcc_unbound_cases.lean').write_text(source)
    print(metadata)
