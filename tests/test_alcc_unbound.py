"""Bounded live tests of the Lean byte/schema composition, not Python refinement."""
from tools.lean_invoke import lean_command
from tools.lean_fixture_format import wrap_source
from tests.lean_test_support import assert_reduction_rejected
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tests.generate_alcc_unbound_cases import generate, wire
from tests.generate_alcc_schema_cases import task, nums

ROOT = Path(__file__).resolve().parents[1]


class ALCCUnboundFixtureTests(unittest.TestCase):
    def test_generated_byte_fixtures_are_current(self):
        source, metadata = generate()
        self.assertEqual(source, (ROOT/'tests/lean/alcc_unbound_cases.lean').read_text())
        self.assertEqual(metadata, dict(positive_pairs=6, syntax_refusals=16,
                                        schema_refusals=7, lean_assertions=74))


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'Live Lean required')
class ALCCUnboundTests(unittest.TestCase):
    def run_lean(self, source):
        if not Path(source).resolve().is_relative_to(ROOT):
            source = Path(source)
            source.write_text(wrap_source(source.read_text()))
        result = subprocess.run(
            lean_command(['-j1', '-DwarningAsError=true', '-DrelaxedAutoImplicit=false', '--json', str(source)], lake='lake'),
            cwd=ROOT, capture_output=True, text=True, timeout=300)
        target = os.environ.get('ALCC_UNBOUND_EVIDENCE_DIR')
        if target:
            out = Path(target); out.mkdir(parents=True, exist_ok=True)
            stem = out / self._testMethodName
            stem.with_suffix('.lean.txt').write_bytes(Path(source).read_bytes())
            stem.with_suffix('.log').write_text(result.stdout + result.stderr)
            stem.with_suffix('.exit-code').write_text(str(result.returncode) + '\n')
        return result

    def test_byte_matrix_and_relational_witnesses(self):
        result = self.run_lean(ROOT/'tests/lean/alcc_unbound_cases.lean')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for name in ['decodeFromBytes_sound', 'unboundTaskRel_deterministic', 'decodeFromBytes_serialized']:
            self.assertIn(name, result.stdout)
        self.assertNotIn('sorryAx', result.stdout)

    def test_noncanonical_acceptance_cannot_be_proved_by_reduction(self):
        p, c = task([], [], [], [])
        with tempfile.TemporaryDirectory(prefix='alcc-unbound-negative-') as tmp:
            source = Path(tmp)/'Invalid.lean'
            source.write_text('import Verification.AlgebraicCertificateUnbound\n'
                              'open AlgebraicCertificateUnbound\n'
                              'set_option maxRecDepth 20000\n'
                              f'example : (decodeFromBytes {nums(b" " + wire(p))} '
                              f'{nums(wire(c))}).isSome = true := by rfl\n')
            result = self.run_lean(source)
        assert_reduction_rejected(self, result)
        self.assertIn('rfl', result.stdout + result.stderr)
        self.assertNotIn('object file', result.stdout + result.stderr)
