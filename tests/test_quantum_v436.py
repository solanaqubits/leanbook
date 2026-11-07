"""Kernel regressions for critical one-sided attraction and subcritical noisy BBPSSW orbits."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV436LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_critical_below_double_root(self):
        self.check_fixture("quantum_critical_below_double")

    def test_critical_above_double_root_and_fixed_endpoints(self):
        self.check_fixture("quantum_critical_above_double")

    def test_subcritical_and_zero_quality(self):
        self.check_fixture("quantum_subcritical_orbits")

    def test_registry_exports(self):
        self.check_fixture("quantum_v436_registry")
