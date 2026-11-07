"""Kernel regressions for post-depolarized BBPSSW operators and fixed-point windows."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV434LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_discriminant_regimes(self):
        self.check_fixture("quantum_noisy_bbpssw_regimes")

    def test_fixed_points_and_exact_window_witness(self):
        self.check_fixture("quantum_noisy_bbpssw_roots")

    def test_operator_channel_trace_and_normalization(self):
        self.check_fixture("quantum_noisy_bbpssw_operator")

    def test_registry_exports(self):
        self.check_fixture("quantum_v434_registry")
