"""Live API applications, exact expectations and counterexamples to omitted premises."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class PrometheusAuditsLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', f'tests/lean/{name}.lean'], lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_stopping_probability_and_error_denominators(self):
        self.check_fixture("prometheus_noise_audit_regression")

    def test_ucn_rates_eos_and_conditional_energy(self):
        self.check_fixture("prometheus_ucn_audit_regression")

    def test_master_registry_exports_both_audits(self):
        self.check_fixture("prometheus_audits_registry")


if __name__ == "__main__":
    unittest.main()
