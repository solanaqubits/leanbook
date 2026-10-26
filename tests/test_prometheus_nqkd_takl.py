"""Kernel regressions for Born-law interception and conditional ring/decay claims."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class PrometheusNQKDTAKLLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', f'tests/lean/{name}.lean'], lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_born_law_noise_and_counterexamples(self):
        self.check_fixture("prometheus_nqkd_regression")

    def test_phase_density_and_ring_counterexamples(self):
        self.check_fixture("prometheus_takl_regression")

    def test_registry_exports(self):
        self.check_fixture("prometheus_nqkd_takl_registry")


if __name__ == "__main__":
    unittest.main()
