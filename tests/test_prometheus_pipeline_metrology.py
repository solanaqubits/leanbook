"""Live queue, covariance, calibration and premise-counterexample checks."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class PrometheusPipelineMetrologyLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, "env", "lean", "-DwarningAsError=true", f"tests/lean/{name}.lean"],
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_derived_parallel_wait_buffer_and_latency(self):
        self.check_fixture("prometheus_pipeline_regression")

    def test_phase_covariance_calibration_and_photon_estimator(self):
        self.check_fixture("prometheus_metrology_regression")

    def test_master_registry_exports_both_modules(self):
        self.check_fixture("prometheus_pipeline_metrology_registry")


if __name__ == "__main__":
    unittest.main()
