"""Scoped schema-decoder tests. No Python decoder or runtime admission is certified."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tests.generate_alcc_schema_cases import generate

ROOT = Path(__file__).resolve().parents[1]


class ALCCSchemaFixtureTests(unittest.TestCase):
    def test_generated_fixtures_are_current(self):
        source, positive, negative = generate()
        self.assertEqual(source, (ROOT/'tests/lean/alcc_schema_cases.lean').read_text())
        self.assertEqual((positive, negative), (10, 48))


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'Live Lean required')
class ALCCSchemaTests(unittest.TestCase):
    def run_lean(self, source):
        result = subprocess.run(
            ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true',
             '-DrelaxedAutoImplicit=false', str(source)],
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        target = os.environ.get('ALCC_SCHEMA_EVIDENCE_DIR')
        if target:
            out = Path(target); out.mkdir(parents=True, exist_ok=True)
            stem = out / self._testMethodName
            stem.with_suffix('.lean.txt').write_bytes(Path(source).read_bytes())
            stem.with_suffix('.log').write_text(result.stdout + result.stderr)
            stem.with_suffix('.exit-code').write_text(str(result.returncode) + '\n')
        return result

    def test_structural_matrix_and_kernel_separation(self):
        result = self.run_lean(ROOT/'tests/lean/alcc_schema_cases.lean')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('decodeSchema_sound', result.stdout)
        self.assertIn('schemaDecodeRel_deterministic', result.stdout)
        self.assertNotIn('sorryAx', result.stdout)

    def test_reducible_fraction_cannot_be_accepted_by_reduction(self):
        with tempfile.TemporaryDirectory(prefix='alcc-schema-negative-') as tmp:
            source = Path(tmp)/'Invalid.lean'
            source.write_text('''import Verification.AlgebraicCertificateSchema
open AlgebraicCertificateSyntax AlgebraicCertificateSchema
example : (decodePoly 0 (.array [.object [
  (bytes "coeff", .array [.number [50], .number [52]]),
  (bytes "powers", .array [])]])).isSome = true := by rfl
''')
            result = self.run_lean(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('rfl', result.stdout + result.stderr)
        self.assertNotIn('object file', result.stdout + result.stderr)
