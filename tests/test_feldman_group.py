"""Live tests for fixed-vector Feldman consistency and threshold recovery."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class FeldmanGroupLiveTests(unittest.TestCase):
    def compile(self, path):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        return subprocess.run([lake, 'env', 'lean', '-j1', '-DwarningAsError=true', str(path)],
                              cwd=ROOT, capture_output=True, text=True, timeout=180)

    def test_finite_field_recovery_and_boundaries(self):
        r = self.compile(ROOT / 'tests/lean/feldman_group_regression.lean')
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_false_share_cannot_be_proved_by_reduction(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / 'FalseShare.lean'
            p.write_text('''import Verification.CryptoFeldmanVSSGroup
open CryptoFeldmanVSSGroup
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
example : Verify (K := ZMod 7) (1 : ZMod 7) 1 (fun _ => 0) 1 1 := by
  norm_num [Verify, evaluateCommitments, Finset.sum_range_succ]
''')
            r = self.compile(p)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn('error:', r.stdout + r.stderr)


if __name__ == '__main__':
    unittest.main()
