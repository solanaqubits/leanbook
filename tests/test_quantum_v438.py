"""Kernel regressions for chronological noisy repeater schedules."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV438LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_operator_schedule(self):
        self.check_fixture("quantum_scheduled_noisy_operator")

    def test_chronology_and_resources(self):
        self.check_fixture("quantum_scheduled_noisy_chronology")

    def test_limits_and_prefix_quality(self):
        self.check_fixture("quantum_scheduled_noisy_quality")

    def test_registry_exports(self):
        self.check_fixture("quantum_v438_registry")
