"""Scoped kernel/model checks; not the 55 SimLab acceptance scenarios."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest
ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'live Lean checks required')
class ActuatorArbitrationTests(unittest.TestCase):
    def check_lean(self, *args):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        p = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', *args],
                           cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        return p.stdout

    def test_arbitration_replay_cas_and_freshness(self):
        self.assertIn('ACTUATOR_ARBITRATION_OK 33', self.check_lean('--run', 'tests/lean/actuator_arbitration_regression.lean'))

    def test_registry_exports_arbitration_suite(self):
        self.check_lean('tests/lean/actuator_arbitration_registry.lean')
