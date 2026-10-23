"""Live kernel regressions for bounded conductance, history and spatial attenuation."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class FungalMyceliumLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, "env", "lean", "-DwarningAsError=true", f"tests/lean/{name}.lean"],
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_conductance_history_spikes_and_spatial_boundaries(self):
        self.check_fixture("fungal_mycelium_regression")

    def test_registry_exports(self):
        self.check_fixture("fungal_mycelium_registry")


if __name__ == "__main__":
    unittest.main()
