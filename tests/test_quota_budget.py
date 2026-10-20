"""Kernel and runtime regressions for constructive quota budgets."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class QuotaBudgetLiveTests(unittest.TestCase):
    def test_minimal_budgets_and_extraction(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true', '--run',
             'tests/lean/quota_budget_regression.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('QUOTA_BUDGET_OK 39', result.stdout)

    def test_master_suite_exports_probability_contract(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true',
             'tests/lean/quota_budget_registry.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
