"""Kernel regressions for Werner cascade matrices, decay and fixed points."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV427LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_scalar_fixed_points_and_limits(self):
        self.check_fixture("quantum_cascade_decay")

    def test_operator_matrix_and_exact_fidelities(self):
        self.check_fixture("quantum_werner_cascade")

    def test_registry_exports(self):
        self.check_fixture("quantum_v427_registry")
