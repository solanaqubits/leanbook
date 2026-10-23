import os,subprocess,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS')=='1','Live Lean tests required')
class FiniteKeyTests(unittest.TestCase):
 def fixture(self,n):
  p=subprocess.run(['lake','env','lean','-j2','-DwarningAsError=true','tests/lean/'+n+'.lean'],cwd=ROOT,capture_output=True,text=True,timeout=180)
  self.assertEqual(p.returncode,0,p.stdout+p.stderr)
 def test_exact_budget_and_guards(self):self.fixture('prometheus_finitekey_regression')
 def test_registry(self):self.fixture('prometheus_finitekey_registry')
