"""Live kernel checks of mean transfer, saturation and explicit remainder accounting."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class OptospintronicLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, "env", "lean", "-DwarningAsError=true", f"tests/lean/{name}.lean"],
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_transfer_saturation_and_remainder_boundaries(self):
        self.check_fixture("optospintronic_regression")

    def test_registry_exports(self):
        self.check_fixture("optospintronic_registry")


if __name__ == "__main__":
    unittest.main()
