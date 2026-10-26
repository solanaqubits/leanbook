"""Live kernel checks for independent causality and executable vector clocks."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class VectorCausalLiveTests(unittest.TestCase):
    def test_causal_reflection_and_operational_regressions(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake, 'lake must be available for live compiler tests')
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', 'tests/lean/vector_causal_regression.lean'], lake=lake),
            cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
