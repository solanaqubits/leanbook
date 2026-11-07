"""Kernel regressions for the seven supercritical noisy BBPSSW orbit regions."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class QuantumV435LiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            elaborate_command(f"tests/lean/{name}.lean", lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_mixing_basin_from_both_sides(self):
        self.check_fixture("quantum_noisy_orbit_mixing")

    def test_ceiling_basin_from_both_sides(self):
        self.check_fixture("quantum_noisy_orbit_ceiling")

    def test_three_stationary_orbits_and_all_index_barriers(self):
        self.check_fixture("quantum_noisy_orbit_stationary")

    def test_registry_exports(self):
        self.check_fixture("quantum_v435_registry")
