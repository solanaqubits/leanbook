"""Stable sorting, counted recursion and consensus backend regressions."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class MarzulloEventSortingLiveTests(unittest.TestCase):
    def test_stable_sort_comparisons_and_consensus(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', 'tests/lean/marzullo_sorting_regression.lean'], lake=lake),
            cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('MARZULLO_SORT_EXEC_OK: 12 cases', result.stdout)


if __name__ == '__main__':
    unittest.main()
