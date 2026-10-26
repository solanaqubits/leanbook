"""Live kernel regressions for repeated-request Ricart–Agrawala safety and progress."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class RicartAgrawalaLiveTests(unittest.TestCase):
    def test_repeated_requests_deferral_reordering_and_conditional_progress(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake, 'lake must be available for live compiler tests')
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', 'tests/lean/ricart_agrawala_regression.lean'], lake=lake),
            cwd=ROOT, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
