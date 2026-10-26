"""Scoped kernel/model checks; not the 33 SimLab acceptance scenarios."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest
ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'live Lean checks required')
class ExternalActuatorTests(unittest.TestCase):
    def check_lean(self, *args):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        p = subprocess.run(lean_command(['-DwarningAsError=true', *args], lake=lake),
                           cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        return p.stdout

    def test_history_and_crash_counterexamples(self):
        self.assertIn('EXTERNAL_ACTUATOR_OK 4', self.check_lean('--run', 'tests/lean/external_actuator_regression.lean'))

    def test_registry_exports_trace_invariant(self):
        self.check_lean('tests/lean/external_actuator_registry.lean')
