"""Exact-content sequential refinement; not SQLite or external-witness qualification."""
import os
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'Enable live Lean tests')
class ReadyPreparedTests(unittest.TestCase):
    def lean(self, *args):
        p = subprocess.run(['lake','env','lean','-j1','-DwarningAsError=true',*args],
                           cwd=ROOT, capture_output=True, text=True, timeout=240)
        self.assertEqual(p.returncode, 0, p.stdout+p.stderr)
        return p.stdout

    def test_crash_boundaries_and_output_simulation(self):
        self.assertIn('READY_PREPARED_OK 30', self.lean(
            '--run', 'tests/lean/provenance_ready_prepared_regression.lean'))

    def test_registry_contract(self):
        self.lean('tests/lean/provenance_ready_prepared_registry.lean')


if __name__ == '__main__':
    unittest.main()
