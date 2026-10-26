"""QCP/01 profile bytes: independent fixed vectors, malformed frames and composition."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class QuotaProfileCodecLiveTests(unittest.TestCase):
    def test_finite_transfer_and_refusals(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(lean_command(['-DwarningAsError=true', '--run', 'tests/lean/quota_profile_codec_regression.lean'], lake=lake),
                                cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('QUOTA_PROFILE_CODEC_OK 79', result.stdout)

    def test_master_suite_exports_profile_contract(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(lean_command(['-DwarningAsError=true', 'tests/lean/quota_profile_codec_registry.lean'], lake=lake),
                                cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
