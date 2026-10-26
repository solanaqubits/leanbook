"""Actual scoped tests of the byte-to-verdict Lean composition."""
from tools.lean_invoke import lean_command
from tools.lean_fixture_format import wrap_source
from tests.lean_test_support import assert_reduction_rejected
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tests.generate_alcc_verify_cases import generate
from tests.generate_alcc_bound_cases import bind
from tests.generate_alcc_schema_cases import task, term, nums
from tests.generate_alcc_unbound_cases import wire

ROOT = Path(__file__).resolve().parents[1]


class ALCCVerifyFixtureTests(unittest.TestCase):
    def test_generated_fixtures_are_current(self):
        source, metadata = generate()
        self.assertEqual(source,(ROOT/'tests/lean/alcc_verify_cases.lean').read_text())
        self.assertEqual(metadata,dict(accepted=4,rejected=3,decoder_refusals=5,
                                      lean_assertions=26,named_computations=12))


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1','Live Lean required')
class ALCCVerifyTests(unittest.TestCase):
    def run_lean(self, source, suffix=''):
        if not Path(source).resolve().is_relative_to(ROOT):
            source = Path(source)
            source.write_text(wrap_source(source.read_text()))
        result = subprocess.run(lean_command(['-j1', '-DwarningAsError=true', '-DrelaxedAutoImplicit=false', '--json', str(source)], lake='lake'),
                                cwd=ROOT,capture_output=True,text=True,timeout=300)
        target = os.environ.get('ALCC_VERIFY_EVIDENCE_DIR')
        if target:
            out=Path(target);out.mkdir(parents=True,exist_ok=True)
            stem=out/(self._testMethodName+suffix)
            stem.with_suffix('.lean.txt').write_bytes(Path(source).read_bytes())
            stem.with_suffix('.log').write_text(result.stdout+result.stderr)
            stem.with_suffix('.exit-code').write_text(str(result.returncode)+'\n')
        return result

    def test_actual_three_way_verdicts_and_semantic_witnesses(self):
        result=self.run_lean(ROOT/'tests/lean/alcc_verify_cases.lean')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        for name in ['verifyCertificateBytes_none_iff','verifyCertificateBytes_true_sound',
                     'verifyCertificateBytes_false_sound']:
            self.assertIn(name,result.stdout)
        self.assertNotIn('sorryAx',result.stdout)

    def test_false_claims_cannot_be_proved_by_reduction(self):
        p,c=bind(task(['x'],[],[term(1,1,[1])],[]))
        # A valid binding with invalid algebra must not yield true.
        # A decoder refusal must not be misreported as a mathematical false verdict.
        claims=[('false_to_true',wire(p),wire(c),'true'),
                ('none_to_false',b' '+wire(p),wire(c),'false')]
        with tempfile.TemporaryDirectory(prefix='alcc-verify-negative-') as tmp:
            for name,bp,bc,verdict in claims:
                source=Path(tmp)/(name+'.lean')
                source.write_text('import Verification.AlgebraicCertificateVerify\n'
                                  'open AlgebraicCertificateVerify\n'
                                  'set_option maxRecDepth 20000\n'
                                  f'example : verifyCertificateBytes {nums(bp)} {nums(bc)} = '
                                  f'some {verdict} := by rfl\n')
                result=self.run_lean(source,'_'+name)
                assert_reduction_rejected(self, result)
                self.assertIn('rfl',result.stdout+result.stderr)
                for unrelated in ['object file','maximum recursion depth','unknown identifier']:
                    self.assertNotIn(unrelated,result.stdout+result.stderr)
