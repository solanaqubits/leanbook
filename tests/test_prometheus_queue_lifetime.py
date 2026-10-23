"""Live variable-queue conservation and finite-law information regressions."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class PrometheusQueueLifetimeLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, "env", "lean", "-DwarningAsError=true", f"tests/lean/{name}.lean"],
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_variable_queue_balance_and_overload(self):
        self.check_fixture("prometheus_variable_queue_regression")

    def test_score_information_and_lifetime_identifiability(self):
        self.check_fixture("prometheus_lifetime_information_regression")

    def test_master_registry_exports_both_modules(self):
        self.check_fixture("prometheus_queue_lifetime_registry")


if __name__ == "__main__":
    unittest.main()
