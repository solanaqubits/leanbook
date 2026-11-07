"""Kernel regressions for nested repeater decay, growth, operators and resource weights."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV433LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_one_round_decay_and_swap_reversal(self):
        self.check_fixture("quantum_nested_decay")

    def test_nested_operator_probability_and_specializations(self):
        self.check_fixture("quantum_nested_operator")

    def test_all_finite_scale_growth_and_resources(self):
        self.check_fixture("quantum_nested_growth")

    def test_registry_exports(self):
        self.check_fixture("quantum_v433_registry")
