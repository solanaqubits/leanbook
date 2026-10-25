"""Live regression for the experimental cached normalizer."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for Lean examples')
class CachedNormalizationTests(unittest.TestCase):
    def test_exact_results_and_order(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'lean', 'tests/lean/alcc_normalize_cached.lean',
                                 '--', '-j1', '-DwarningAsError=true'],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
