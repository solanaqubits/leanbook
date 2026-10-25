"""Scoped Lean tests: SHA vectors, binding, and rejection of false proof claims."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tests.generate_alcc_bound_cases import generate
from tests.generate_alcc_schema_cases import task, nums
from tests.generate_alcc_unbound_cases import wire

ROOT = Path(__file__).resolve().parents[1]


class ALCCBoundFixtureTests(unittest.TestCase):
    def test_generated_fixtures_are_current(self):
        sources, metadata = generate()
        for name, source in sources.items():
            self.assertEqual(source, (ROOT/f'tests/lean/alcc_{name}_cases.lean').read_text())
        self.assertEqual(metadata, dict(nist_vectors=10, positive_pairs=4, negative_pairs=12,
                                        sha_assertions=17, bound_assertions=35))


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'Live Lean required')
class ALCCBoundTests(unittest.TestCase):
    def run_lean(self, source, suffix=''):
        result = subprocess.run(
            ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true',
             '-DrelaxedAutoImplicit=false', str(source)],
            cwd=ROOT, capture_output=True, text=True, timeout=300)
        target = os.environ.get('ALCC_BOUND_EVIDENCE_DIR')
        if target:
            out = Path(target); out.mkdir(parents=True, exist_ok=True)
            stem = out / (self._testMethodName + suffix)
            stem.with_suffix('.lean.txt').write_bytes(Path(source).read_bytes())
            stem.with_suffix('.log').write_text(result.stdout + result.stderr)
            stem.with_suffix('.exit-code').write_text(str(result.returncode) + '\n')
        return result

    def test_nist_vectors_and_sha_primitives(self):
        result = self.run_lean(ROOT/'tests/lean/alcc_sha256_cases.lean')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('sha256_refines', result.stdout)
        self.assertNotIn('sorryAx', result.stdout)

    def test_bound_byte_matrix_and_relational_witnesses(self):
        result = self.run_lean(ROOT/'tests/lean/alcc_bound_cases.lean')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('decodeBoundTask_sound', result.stdout)
        self.assertIn('boundTaskRel_deterministic', result.stdout)
        self.assertNotIn('sorryAx', result.stdout)

    def test_false_digest_and_forged_acceptance_are_not_provable(self):
        p, c = task([], [], [], [])  # Equal zero identifiers, invalid self-hash.
        claims = [
            ('digest', 'example : AlgebraicCertificateSHA256.SHA256Bytes [] = [] := by rfl\n'),
            ('binding', f'example : (AlgebraicCertificateBound.decodeBoundTask {nums(wire(p))} '
                        f'{nums(wire(c))}).isSome = true := by rfl\n')]
        with tempfile.TemporaryDirectory(prefix='alcc-bound-negative-') as tmp:
            for name, claim in claims:
                source = Path(tmp)/f'Invalid_{name}.lean'
                source.write_text('import Verification.AlgebraicCertificateBound\n'
                                  'set_option maxRecDepth 20000\n' + claim)
                result = self.run_lean(source, '_' + name)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('rfl', result.stdout + result.stderr)
                for unrelated in ['object file', 'maximum recursion depth', 'unknown identifier']:
                    self.assertNotIn(unrelated, result.stdout + result.stderr)
