"""Generate explicit Lean AST/schema cases with Python's standard library only.

Expected structures are direct positional fixtures, not decoder outputs.
No JSON parser, hash computation or external CAS is trusted by these tests.
"""
from copy import deepcopy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def term(num, den, powers):
    return {'coeff': [num, den], 'powers': powers}


def task(variables, hypotheses, target, multipliers):
    header = {'format_version': '1.0', 'profile_id': 'ALCC-JSON-1', 'problem_id': '0' * 64}
    return (dict(header, variables=variables,
                 hypotheses=[{'id': f'h{i}', 'poly': p} for i, p in enumerate(hypotheses)],
                 target={'poly': target}),
            dict(header, multipliers=[{'hypothesis_id': f'h{i}', 'poly': p}
                                      for i, p in enumerate(multipliers)]))


def nums(xs):
    return '[' + ','.join(map(str, xs)) + ']'


def ast(x):
    if isinstance(x, tuple):
        kind, value = x
        if kind == 'number':
            return f'(.number {nums(list(value.encode("ascii")))})'
        if kind == 'object':
            return obj(value)
        if kind == 'bytes':
            return f'(.string {nums(value)})'
    if isinstance(x, bool):
        return '.boolean ' + str(x).lower()
    if isinstance(x, int):
        return f'(.number {nums(list(str(x).encode("ascii")))})'
    if isinstance(x, str):
        return f'(.string {nums(list(x.encode("ascii")))})'
    if isinstance(x, list):
        return '(.array [' + ','.join(ast(v) for v in x) + '])'
    if isinstance(x, dict):
        return obj(sorted(x.items()))
    if x is None:
        return '.null'
    raise TypeError(x)


def obj(pairs):
    return '(.object [' + ','.join(f'({nums(list(k.encode("ascii")))},{ast(v)})'
                                  for k, v in pairs) + '])'


def poly_view(p):
    return '[' + ','.join(f'({nums(t["powers"])},({t["coeff"][0]} : ℚ) / {t["coeff"][1]})'
                          for t in p) + ']'


def view(p, c):
    hs = '[' + ','.join(poly_view(h['poly']) for h in p['hypotheses']) + ']'
    qs = '[' + ','.join(poly_view(h['poly']) for h in c['multipliers']) + ']'
    return f'⟨{len(p["variables"])},{len(p["hypotheses"])},{poly_view(p["target"]["poly"])},{hs},{qs}⟩'


def generate():
    baseline = task(['x', 'y', 'z'],
                    [[term(1, 1, [2, 0, 0]), term(-1, 1, [0, 1, 0])],
                     [term(1, 1, [0, 2, 0]), term(-1, 1, [0, 0, 1])]],
                    [term(1, 1, [4, 0, 0]), term(-1, 1, [0, 0, 1])],
                    [[term(1, 1, [2, 0, 0]), term(1, 1, [0, 1, 0])],
                     [term(1, 1, [0, 0, 0])]])
    positive = [('empty', task([], [], [], [])), ('reference', baseline),
                ('fraction', task(['x'], [[term(-1, 2, [1])]],
                                  [term(3, 4, [1])], [[term(-3, 2, [0])]])),
                ('constant', task([], [[term(1, 2, [])]], [term(1, 4, [])],
                                  [[term(1, 2, [])]])),
                ('zero_hypothesis', task(['x'], [[]], [], [[term(1, 1, [1])]])),
                ('variable_positions', task(['z', 'a'], [[term(1, 1, [0, 1])]],
                                           [term(1, 1, [0, 1])], [[term(1, 1, [0, 0])]])),
                ('empty_hypotheses_nonzero_target', task(['x'], [], [term(1, 1, [1])], []))]
    altered = deepcopy(baseline)
    altered[1]['multipliers'][0]['poly'].append(term(1, 1, [0, 0, 0]))
    positive.append(('schema_valid_identity_invalid', altered))
    different = deepcopy(baseline); different[1]['problem_id'] = 'f' * 64
    positive.append(('different_unbound_digests', different))
    syzygy = deepcopy(baseline)
    syzygy[1]['multipliers'][0]['poly'] = [term(1, 1, [2, 0, 0]), term(1, 1, [0, 2, 0]),
                                        term(1, 1, [0, 1, 0]), term(-1, 1, [0, 0, 1])]
    syzygy[1]['multipliers'][1]['poly'] = [term(-1, 1, [2, 0, 0]), term(1, 1, [0, 1, 0]),
                                        term(1, 1, [0, 0, 0])]
    positive.append(('syzygy', syzygy))
    negative = []

    def bad(name, mutate):
        p, c = deepcopy(baseline); mutate(p, c); negative.append((name, (p, c)))

    bad('reducible', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=[2, 4]))
    bad('zero_numerator', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=[0, 1]))
    bad('zero_denominator', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=[1, 0]))
    bad('negative_denominator', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=[1, -2]))
    bad('scalar_coefficient', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=1))
    bad('string_coefficient', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff='1/2'))
    bad('long_coefficient_pair', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=[1, 1, 1]))
    for name, token in [('float', '1.0'), ('exponent', '1e0'), ('leading_zero', '01'),
                        ('negative_zero', '-0'), ('positive_sign', '+1')]:
        bad(name, lambda p, c, tok=token: c['multipliers'][0]['poly'][0].update(coeff=[('number', tok), 1]))
    bad('boolean_number', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=[True, 1]))
    bad('short_vector', lambda p, c: c['multipliers'][0]['poly'][0].update(powers=[2, 0]))
    bad('long_vector', lambda p, c: c['multipliers'][0]['poly'][0].update(powers=[2, 0, 0, 0]))
    bad('negative_power', lambda p, c: c['multipliers'][0]['poly'][0].update(powers=[-1, 0, 0]))
    bad('power_limit', lambda p, c: c['multipliers'][0]['poly'][0].update(powers=[65, 0, 0]))
    bad('degree_limit', lambda p, c: c['multipliers'][0]['poly'][0].update(powers=[64, 64, 1]))
    bad('coefficient_limit', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=[2**256, 1]))
    bad('denominator_limit', lambda p, c: c['multipliers'][0]['poly'][0].update(coeff=[1, 2**256]))
    bad('reversed_terms', lambda p, c: c['multipliers'][0]['poly'].reverse())
    bad('duplicate_terms', lambda p, c: c['multipliers'][0]['poly'].append(c['multipliers'][0]['poly'][0]))
    bad('duplicate_variables', lambda p, c: p.update(variables=['x', 'x', 'z']))
    bad('bad_identifier', lambda p, c: p.update(variables=['x-y', 'y', 'z']))
    bad('empty_identifier', lambda p, c: p.update(variables=['', 'y', 'z']))
    bad('long_identifier', lambda p, c: p.update(variables=['x'*65, 'y', 'z']))
    bad('nonascii_identifier', lambda p, c: p.update(variables=[('bytes', [128]), 'y', 'z']))
    bad('duplicate_hypothesis_ids', lambda p, c: p['hypotheses'][1].update(id='h0'))
    bad('wrong_multiplier_id', lambda p, c: c['multipliers'][0].update(hypothesis_id='h1'))
    bad('permuted_multipliers', lambda p, c: c['multipliers'].reverse())
    bad('missing_multiplier', lambda p, c: c['multipliers'].pop())
    bad('extra_multiplier', lambda p, c: c['multipliers'].append(c['multipliers'][0]))
    bad('passport_extra', lambda p, c: p.update(extra=0))
    bad('certificate_extra', lambda p, c: c.update(extra=0))
    bad('term_extra', lambda p, c: c['multipliers'][0]['poly'][0].update(extra=0))
    bad('target_extra', lambda p, c: p['target'].update(extra=0))
    bad('hypothesis_extra', lambda p, c: p['hypotheses'][0].update(extra=0))
    bad('missing_profile', lambda p, c: p.pop('profile_id'))
    bad('wrong_profile', lambda p, c: c.update(profile_id='ALCC-JSON-2'))
    bad('wrong_version', lambda p, c: p.update(format_version='2.0'))
    bad('missing_digest', lambda p, c: c.pop('problem_id'))
    bad('short_digest', lambda p, c: c.update(problem_id='0'))
    bad('uppercase_digest', lambda p, c: c.update(problem_id='A'*64))
    bad('variables_limit', lambda p, c: p.update(variables=[f'v{i}' for i in range(17)]))
    for name, pairs in [('duplicate_object_key', [('format_version', '1.0')]+sorted(baseline[0].items())),
                        ('unordered_object', list(reversed(sorted(baseline[0].items()))))]:
        negative.append((name, (('object', pairs), baseline[1])))
    many = task([], [[] for _ in range(33)], [], [[] for _ in range(33)])
    negative.append(('hypotheses_limit', many))
    monomials = [term(1, 1, [a, b]) for a in range(4, -1, -1) for b in range(64, -1, -1)][:257]
    negative.append(('monomials_limit', task(['a', 'b'], [monomials], [], [[]])))

    header = '''import Verification.AlgebraicCertificateSchema
open AlgebraicCertificateSyntax AlgebraicCertificateKernel AlgebraicCertificateSchema
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ALCCSchemaCases
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
'''
    lines = [header]
    for name, (p, c) in positive:
        lines += [f'def p_{name} : JsonAST := {ast(p)}', f'def c_{name} : JsonAST := {ast(c)}',
                  f'example : (decodeSchema p_{name} c_{name}).map taskView = some {view(p,c)} := by decide +kernel']
    for name, (p, c) in negative:
        lines += [f'-- Reject: {name}',
                  f'example : (decodeSchema {ast(p)} {ast(c)}).isNone = true := by decide +kernel']
    lines += ['''example : (decodeSchema p_reference c_reference).map
    (fun t => checkCert t.2.2.1 t.2.2.2) = some true := by decide +kernel
example : (decodeSchema p_schema_valid_identity_invalid c_schema_valid_identity_invalid).map
    (fun t => checkCert t.2.2.1 t.2.2.2) = some false := by decide +kernel
example {jp jc : JsonAST} {t : UnboundTask} (h : decodeSchema jp jc = some t) :
    SchemaDecodeRel jp jc t := decodeSchema_sound h
example {jp jc : JsonAST} {a b : UnboundTask}
    (ha : SchemaDecodeRel jp jc a) (hb : SchemaDecodeRel jp jc b) : a = b :=
  schemaDecodeRel_deterministic ha hb
#print axioms decodeSchema_sound
#print axioms schemaDecodeRel_deterministic
#print axioms decodePoly_at
end ALCCSchemaCases
''']
    return '\n'.join(lines), len(positive), len(negative)


if __name__ == '__main__':
    source, positive, negative = generate()
    (ROOT/'tests/lean/alcc_schema_cases.lean').write_text(source)
    print(f'{positive} positive structural fixtures; {negative} rejection cases; {positive+negative+4} Lean examples')
