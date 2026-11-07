"""Kernel regressions for BBPSSW limits, complete binary tree weights and registry."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV430LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_orbit_limits_and_barriers(self):
        self.check_fixture("quantum_bbpssw_convergence")

    def test_binary_tree_probability_and_operator(self):
        self.check_fixture("quantum_bbpssw_tree")

    def test_registry_exports(self):
        self.check_fixture("quantum_v430_registry")
