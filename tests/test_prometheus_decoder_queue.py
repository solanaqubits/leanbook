"""Kernel applications, independent exact values and premise counterexamples."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class PrometheusDecoderQueueLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, "env", "lean", "-DwarningAsError=true", f"tests/lean/{name}.lean"],
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_queue_identities_bounds_counterexamples_and_budget(self):
        self.check_fixture("prometheus_decoder_queue_regression")

    def test_master_registry_exports_queue(self):
        self.check_fixture("prometheus_decoder_queue_registry")


if __name__ == "__main__":
    unittest.main()
