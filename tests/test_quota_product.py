"""Kernel and runtime regressions for factorized quota bounds."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class QuotaProductLiveTests(unittest.TestCase):
    def test_products_budgets_and_extraction(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', '--run', 'tests/lean/quota_product_regression.lean'], lake=lake),
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('QUOTA_PRODUCT_OK 28', result.stdout)

    def test_master_suite_exports_probability_contract(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', 'tests/lean/quota_product_registry.lean'], lake=lake),
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
