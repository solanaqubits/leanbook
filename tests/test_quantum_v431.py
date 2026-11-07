"""Kernel regressions for heterogeneous BBPSSW and swap-then-purify."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV431LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_heterogeneous_threshold_and_singular_input(self):
        self.check_fixture("quantum_hetero_threshold")

    def test_operator_normalization_and_swap_bridge(self):
        self.check_fixture("quantum_hetero_operator")

    def test_swap_recovery_depth(self):
        self.check_fixture("quantum_swap_purify_depth")

    def test_registry_exports(self):
        self.check_fixture("quantum_v431_registry")
