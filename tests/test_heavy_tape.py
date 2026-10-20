"""Kernel and runtime regressions for weighted heavy tapes."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class HeavyTapeLiveTests(unittest.TestCase):
    def test_execution_prefixes_and_rejections(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true', '--run',
             'tests/lean/heavy_tape_regression.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('HEAVY_TAPE_OK 16', result.stdout)

    def test_master_suite_exports_probability_contract(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true',
             'tests/lean/heavy_tape_registry.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
