"""Live exact-value, transition and domain-boundary tests for the new finance batch."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest
ROOT = Path(__file__).resolve().parents[1]
@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1", "Enable live Lean checks")
class FinanceBatchTests(unittest.TestCase):
    def compile_case(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        r = subprocess.run([lake, "lean", str(ROOT / "tests/lean" / (name + "_regression.lean")),
                            "--", "-j1", "-DwarningAsError=true"],
                           cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
    def test_amm_exact_output(self):
        self.compile_case("amm_exact_output")
    def test_amm_integer(self):
        self.compile_case("amm_integer")
    def test_stateful_routing(self):
        self.compile_case("stateful_routing")
    def test_route_selection(self):
        self.compile_case("route_selection")
    def test_lending_transitions(self):
        self.compile_case("lending_transitions")
