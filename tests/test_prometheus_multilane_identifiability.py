"""Live kernel regressions, including equality and singular controls."""
import os,subprocess,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS')=='1','Live Lean tests required')
class MultiLaneMetrologyTests(unittest.TestCase):
 def check_fixture(self,name):
  r=subprocess.run(['lake','env','lean','-j2','-DwarningAsError=true','tests/lean/'+name+'.lean'],cwd=ROOT,text=True,capture_output=True,timeout=180)
  self.assertEqual(r.returncode,0,r.stdout+r.stderr)
 def test_vector_and_overload(self):self.check_fixture('prometheus_multilane_regression')
 def test_fisher_and_confounding(self):self.check_fixture('prometheus_identifiability_regression')
 def test_registry(self):self.check_fixture('prometheus_multilane_registry')
