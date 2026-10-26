"""Live kernel regressions for FROST sessions, threshold interpolation and response tampering."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class FrostGroupLiveTests(unittest.TestCase):
    def test_sessions_coalitions_canonicalization_and_tampering(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake, 'lake must be available for live compiler tests')
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', 'tests/lean/frost_group_regression.lean'], lake=lake),
            cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
