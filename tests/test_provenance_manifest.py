"""QPM/01 manifest: independent bytes, strict malformed-frame refusals and registry."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class ProvenanceManifestLiveTests(unittest.TestCase):
    def test_finite_transfer_and_refusals(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(lean_command(['-DwarningAsError=true', '--run', 'tests/lean/provenance_manifest_regression.lean'], lake=lake),
                                cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('PROVENANCE_MANIFEST_OK 161', result.stdout)

    def test_master_suite_exports_profile_contract(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(lean_command(['-DwarningAsError=true', 'tests/lean/provenance_manifest_registry.lean'], lake=lake),
                                cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
