"""Kernel regressions for conditional cascade probabilities and registry wiring."""
import os,subprocess,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS')=='1','Live Lean tests required')
class CascadedFECTests(unittest.TestCase):
    def check_fixture(self,name):
        r=subprocess.run(['lake','env','lean','-j2','-DwarningAsError=true','tests/lean/'+name+'.lean'],cwd=ROOT,text=True,capture_output=True,timeout=180)
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_erasure_majority_and_byte_edges(self):self.check_fixture('prometheus_cascaded_votes')
    def test_conditional_tail_and_crc_scope(self):self.check_fixture('prometheus_cascaded_bound')
    def test_master_registry_exports_suite(self):self.check_fixture('prometheus_cascaded_registry')
if __name__=='__main__':unittest.main()
