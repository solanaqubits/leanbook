"""Byte-to-verdict fixtures with manually specified algebraic expectations.

stdlib JSON/hashlib prepare inputs, never proof terms or expected algebraic verdicts.
"""
from tools.lean_fixture_format import wrap_source
from copy import deepcopy
from pathlib import Path
from tests.generate_alcc_bound_cases import bind
from tests.generate_alcc_schema_cases import task, term, nums
from tests.generate_alcc_unbound_cases import wire

ROOT = Path(__file__).resolve().parents[1]


def generate():
    reference = task(['x', 'y', 'z'],
                     [[term(1, 1, [2, 0, 0]), term(-1, 1, [0, 1, 0])],
                      [term(1, 1, [0, 2, 0]), term(-1, 1, [0, 0, 1])]],
                     [term(1, 1, [4, 0, 0]), term(-1, 1, [0, 0, 1])],
                     [[term(1, 1, [2, 0, 0]), term(1, 1, [0, 1, 0])],
                      [term(1, 1, [0, 0, 0])]])
    syzygy = deepcopy(reference)
    syzygy[1]['multipliers'][0]['poly'] = [term(1,1,[2,0,0]),term(1,1,[0,2,0]),
                                          term(1,1,[0,1,0]),term(-1,1,[0,0,1])]
    syzygy[1]['multipliers'][1]['poly'] = [term(-1,1,[2,0,0]),term(1,1,[0,1,0]),
                                          term(1,1,[0,0,0])]
    accepted = [('empty', bind(task([], [], [], []))), ('reference', bind(reference)),
                ('fraction', bind(task(['z','a'], [[term(-1,2,[0,1])]],
                                       [term(3,4,[0,1])], [[term(-3,2,[0,0])]]))),
                ('syzygy', bind(syzygy))]
    changed = deepcopy(reference)
    changed[1]['multipliers'][0]['poly'].append(term(1,1,[0,0,0]))
    powers = deepcopy(reference)
    powers[1]['multipliers'][0]['poly'][0]['powers'] = [0,2,0]
    rejected = [('added_constant', bind(changed)), ('changed_powers', bind(powers)),
                ('nonzero_no_hypotheses', bind(task(['x'], [], [term(1,1,[1])], [])))]
    p,c = bind(reference)
    bad_schema = deepcopy(c);bad_schema['multipliers'][0]['poly'][0]['coeff']=[2,4]
    bad_body=deepcopy(p);bad_body['target']['poly'][0]['coeff']=[2,1]
    foreign=deepcopy(c);foreign['problem_id']='f'*64
    forged=task([],[],[],[])
    refused=[('syntax_space', b' '+wire(p), wire(c)),
             ('reducible_fraction',wire(p),wire(bad_schema)),
             ('changed_body_hash',wire(bad_body),wire(c)),
             ('foreign_certificate',wire(p),wire(foreign)),
             ('forged_equal_ids',wire(forged[0]),wire(forged[1]))]
    lines=['''import Verification.AlgebraicCertificateVerify
open AlgebraicCertificateSyntax AlgebraicCertificateSchema AlgebraicCertificateBound
open AlgebraicCertificateVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ALCCVerifyCases
''']
    for verdict, cases in [('true',accepted),('false',rejected)]:
        for name,(p,c) in cases:
            lines += [f'def p_{name} : Bytes := {nums(wire(p))}',
                      f'def c_{name} : Bytes := {nums(wire(c))}',
                      f'theorem verdict_{name} : verifyCertificateBytes p_{name} c_{name} = some {verdict} := by decide +kernel',
                      f'example : ∃ t, BoundTaskRel p_{name} c_{name} t ∧ delta t {"=" if verdict=="true" else "≠"} 0 :=',
                      f'  verifyCertificateBytes_{verdict}_sound verdict_{name}']
    for name,p,c in refused:
        lines += [f'def p_{name} : Bytes := {nums(p)}',f'def c_{name} : Bytes := {nums(c)}',
                  f'theorem verdict_{name} : verifyCertificateBytes p_{name} c_{name} = none := by decide +kernel',
                  f'example : decodeBoundTask p_{name} c_{name} = none :=',
                  f'  (verifyCertificateBytes_none_iff _ _).mp verdict_{name}']
    lines += ['''-- One expected passport, both a valid and an invalid supplied certificate.
example : p_reference = p_added_constant := by decide +kernel
example : p_reference = p_changed_powers := by decide +kernel
#print axioms verifyCertificateBytes_none_iff
#print axioms verifyCertificateBytes_true_sound
#print axioms verifyCertificateBytes_false_sound
end ALCCVerifyCases
''']
    return wrap_source('\n'.join(lines)), dict(accepted=4,rejected=3,decoder_refusals=5,
                                  lean_assertions=26,named_computations=12)


if __name__ == '__main__':
    source, metadata = generate()
    (ROOT/'tests/lean/alcc_verify_cases.lean').write_text(source)
    print(metadata)
