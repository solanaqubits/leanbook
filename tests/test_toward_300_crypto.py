"""Live finite-field witnesses and boundary counterexamples for the new crypto batch."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest
ROOT = Path(__file__).resolve().parents[1]
@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1", "Enable live Lean checks")
class CryptoBatchTests(unittest.TestCase):
    def compile_case(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        r = subprocess.run([lake, "lean", str(ROOT / "tests/lean" / (name + "_regression.lean")),
                            "--", "-j1", "-DwarningAsError=true"],
                           cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
    def test_pedersen_vss(self):
        self.compile_case("pedersen_vss")
    def test_shamir_refresh(self):
        self.compile_case("shamir_refresh")
    def test_shamir_repair(self):
        self.compile_case("shamir_repair")
    def test_threshold_bls(self):
        self.compile_case("threshold_bls")
    def test_qualified_sharing(self):
        self.compile_case("qualified_sharing")
    def test_kzg_equation(self):
        self.compile_case("kzg_equation")
    def test_groth16_pairing(self):
        self.compile_case("groth16_pairing")
