"""Live entropy/kernel applications, independent values, and premise counterexamples."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
                     "Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks")
class PrometheusChannelInjectorLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(
            lean_command(['-DwarningAsError=true', f'tests/lean/{name}.lean'], lake=lake),
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_entropy_kernel_rate_latency_and_energy(self):
        self.check_fixture("prometheus_channel_injector_regression")

    def test_master_registry_exports_channel_and_injector(self):
        self.check_fixture("prometheus_channel_injector_registry")


if __name__ == "__main__":
    unittest.main()
