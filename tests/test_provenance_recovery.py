"""Pure sequential recovery: no real disk, cryptographic or concurrency guarantee."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class ProvenanceRecoveryLiveTests(unittest.TestCase):
    def run_lean(self, *args):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(lean_command(['-j1', '-DwarningAsError=true', *args], lake=lake),
                                cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_crash_boundaries_and_content_binding(self):
        self.assertIn('PROVENANCE_RECOVERY_OK 54', self.run_lean(
            '--run', 'tests/lean/provenance_recovery_regression.lean'))

    def test_registry_exports_recovery_obligations(self):
        self.run_lean('tests/lean/provenance_recovery_registry.lean')


if __name__ == '__main__':
    unittest.main()
