"""Actual kernel regression examples for probability premises and exact schedule."""
from tools.lean_invoke import lean_command
import os,subprocess,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS')=='1','Live Lean tests required')
class JitterCycleTests(unittest.TestCase):
 def fixture(self,name):
  p=subprocess.run(lean_command(['-j2', '-DwarningAsError=true', 'tests/lean/' + name + '.lean'], lake='lake'),cwd=ROOT,capture_output=True,text=True,timeout=180)
  self.assertEqual(p.returncode,0,p.stdout+p.stderr)
 def test_probability_premises(self):self.fixture('prometheus_jitter_regression')
 def test_termination_and_clock(self):self.fixture('prometheus_cycle_regression')
 def test_registry(self):self.fixture('prometheus_jitter_cycle_registry')
