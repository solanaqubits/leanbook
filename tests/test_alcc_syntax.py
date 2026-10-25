"""Autonomous ALCC-SYNTAX-1 tests; no Python/JSON bridge or CAS dependency."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'Live Lean required')
class ALCCSyntaxTests(unittest.TestCase):
    def run_lean(self, source):
        result = subprocess.run(
            ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true',
             '-DrelaxedAutoImplicit=false', str(source)],
            cwd=ROOT, capture_output=True, text=True, timeout=180)
        target = os.environ.get('ALCC_SYNTAX_EVIDENCE_DIR')
        if target:
            out = Path(target); out.mkdir(parents=True, exist_ok=True)
            stem = out / self._testMethodName
            stem.with_suffix('.lean.txt').write_bytes(Path(source).read_bytes())
            stem.with_suffix('.log').write_text(result.stdout + result.stderr)
            stem.with_suffix('.exit-code').write_text(str(result.returncode) + '\n')
        return result

    def test_examples_and_ascii_table(self):
        result = self.run_lean(ROOT/'tests/lean/alcc_syntax_cases.lean')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('parseCanonical_complete', result.stdout)
        self.assertNotIn('sorryAx', result.stdout)

    def test_noncanonical_acceptance_cannot_be_proved_by_reduction(self):
        with tempfile.TemporaryDirectory(prefix='alcc-syntax-negative-') as tmp:
            source = Path(tmp)/'Invalid.lean'
            source.write_text('''import Verification.AlgebraicCertificateSyntax
open AlgebraicCertificateSyntax
example : parseCanonical [32,91,93] = some (.array []) := by rfl
''')
            result = self.run_lean(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('rfl', result.stdout + result.stderr)
        self.assertNotIn('object file', result.stdout + result.stderr)
