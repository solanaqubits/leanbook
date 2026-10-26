"""Kernel and runtime regressions for two-tree IPA public scalar binding."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class IPAPublicScalarLiveTests(unittest.TestCase):
    def test_public_scalar_resources_and_extraction(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', '--run', 'tests/lean/ipa_public_scalar_regression.lean'], lake=lake),
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('IPA_PUBLIC_SCALAR_OK 16', result.stdout)

    def test_master_suite_exports_probability_contract(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', 'tests/lean/ipa_public_scalar_registry.lean'], lake=lake),
            cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
