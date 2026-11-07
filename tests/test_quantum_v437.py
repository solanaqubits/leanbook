"""Kernel regressions for noisy BBPSSW resource trees and post-swap recovery barriers."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV437LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_operator_tree_and_actual_swap(self):
        self.check_fixture("quantum_noisy_tree_operator")

    def test_weights_and_noise_endpoints(self):
        self.check_fixture("quantum_noisy_tree_weights")

    def test_exact_recovery_criterion(self):
        self.check_fixture("quantum_noisy_tree_recovery")

    def test_registry_exports(self):
        self.check_fixture("quantum_v437_registry")
