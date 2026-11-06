"""Kernel regressions for independent stages and a nonfactorizing post-measurement interaction."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV423LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_tensor_stages_with_heterogeneous_environment_channels(self):
        self.check_fixture("quantum_tensor_stage_regression")

    def test_post_analyzer_coupling_and_pure_nonproduct_witness(self):
        self.check_fixture("quantum_post_bsm_regression")

    def test_registry_exports(self):
        self.check_fixture("quantum_v423_registry")
