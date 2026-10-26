"""Live kernel checks for ideal MZI action and the registered convention bridge."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class MZIChiralLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', f'tests/lean/{name}.lean'], lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_action_routing_and_boundaries(self):
        self.check_fixture("mzi_chiral_regression")

    def test_registry_and_convention_bridge(self):
        self.check_fixture("mzi_chiral_registry")


if __name__ == "__main__":
    unittest.main()
