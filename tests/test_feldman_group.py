"""Live tests for fixed-vector Feldman consistency and threshold recovery."""
import os
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class FeldmanGroupLiveTests(unittest.TestCase):
    def compile(self, path, json_output=False):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        args = [lake, 'lean', str(path), '--', '-j1', '-DwarningAsError=true']
        if json_output:
            args.append('--json')
        return subprocess.run(args,
                              cwd=ROOT, capture_output=True, text=True, timeout=180)

    def test_finite_field_recovery_and_boundaries(self):
        r = self.compile(ROOT / 'tests/lean/feldman_group_regression.lean')
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_false_share_cannot_be_proved_by_reduction(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / 'FalseShare.lean'
            source = '''import Verification.CryptoFeldmanVSSGroup
open CryptoFeldmanVSSGroup
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
example : Verify (K := ZMod 7) (1 : ZMod 7) 1 (fun _ => 0) 1 SHARE := by
  norm_num [Verify, evaluateCommitments, Finset.sum_range_succ]
'''
            p.write_text(source.replace('SHARE', '0'))
            control = self.compile(p)
            self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
            p.write_text(source.replace('SHARE', '1'))
            r = self.compile(p, json_output=True)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            messages = [json.loads(line) for line in r.stdout.splitlines()
                        if line.startswith('{')]
            errors = [m for m in messages if m.get('severity') == 'error']
            self.assertEqual(len(errors), 1, r.stdout + r.stderr)
            self.assertIn('unsolved goals', errors[0]['data'])
            self.assertIn('⊢ False', errors[0]['data'])


if __name__ == '__main__':
    unittest.main()
