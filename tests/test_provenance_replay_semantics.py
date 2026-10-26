"""Checked contract examples referencing existing ε262, not a runtime proof."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import re
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Enable live Lean checks')
class ReplaySemanticsTests(unittest.TestCase):
    def test_contract_examples_and_axiom_dependencies(self):
        p = subprocess.run(lean_command(['-j1', '-DwarningAsError=true', 'tests/lean/provenance_replay_semantics.lean'], lake='lake'), cwd=ROOT,
                           capture_output=True, text=True, timeout=240)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        declarations = re.findall(r"'ReplaySemanticsRegression\.(\w+)'", p.stdout)
        self.assertEqual(set(declarations), {
            'historical_preserves_consumption', 'historical_uses_pinned_context',
            'matching_retry_returns_history', 'different_digest_rejected',
            'no_second_consumption_after_history', 'response_loss_retains_record',
            'refusal_preserves_consumption', 'historical_report_stays_blocked'})
        self.assertEqual(len(declarations), 8)
        for group in re.findall(r'depends on axioms: \[([^]]*)\]', p.stdout):
            axioms = {x.strip() for x in group.split(',') if x.strip()}
            self.assertLessEqual(axioms, {'propext', 'Classical.choice', 'Quot.sound'})


if __name__ == '__main__':
    unittest.main()
