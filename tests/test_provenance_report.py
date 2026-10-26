"""Pure provenance policy checks; synthetic callbacks are not crypto validation."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class ProvenanceReportLiveTests(unittest.TestCase):
    def run_lean(self, *args):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(lean_command(['-j1', '-DwarningAsError=true', *args], lake=lake),
                                cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_acceptance_refusals_and_trust_boundary(self):
        self.assertIn('PROVENANCE_REPORT_OK 69', self.run_lean(
            '--run', 'tests/lean/provenance_report_regression.lean'))

    def test_registry_exports_verifier_contract(self):
        self.run_lean('tests/lean/provenance_report_registry.lean')


if __name__ == '__main__':
    unittest.main()
