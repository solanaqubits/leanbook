"""Kernel and runtime regressions for counted resumable quota search."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class QuotaResumeCostLiveTests(unittest.TestCase):
    def test_counters_results_and_additivity(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true', '--run',
             'tests/lean/quota_resume_cost_regression.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('QUOTA_RESUME_COST_OK 30', result.stdout)

    def test_master_suite_exports_probability_contract(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true',
             'tests/lean/quota_resume_cost_registry.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
