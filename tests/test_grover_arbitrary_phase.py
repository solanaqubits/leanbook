"""Live regressions for complex phase unitarity, invariant planes and exact probabilities."""
from tools.lean_invoke import lean_command

import os
from pathlib import Path
import shutil
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(
    os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
    "Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests",
)
class GroverArbitraryPhaseLiveTests(unittest.TestCase):
    def test_unitarity_plane_probability_and_signed_legacy_bridge(self):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake, "lake must be available for live compiler tests")
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', 'tests/lean/grover_arbitrary_phase_regression.lean'], lake=lake),
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
