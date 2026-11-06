"""Kernel regressions for marginal reduction and a GHZ probability obstruction."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV422LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_decoupled_arbitrary_inputs_and_nonunital_environment(self):
        self.check_fixture("quantum_decoupled_regression")

    def test_ghz_probability_shift_and_obstruction(self):
        self.check_fixture("quantum_probability_regression")

    def test_registry_exports(self):
        self.check_fixture("quantum_v422_registry")
