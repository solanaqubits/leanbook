"""Targeted kernel applications and countermodels for epsilon201."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1", "Enable live Lean tests")
class HCTKScalarPartitionTests(unittest.TestCase):
    def test_exact_partition_transfer_regularization_and_countermodels(self):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(lean_command(['-DwarningAsError=true', 'tests/lean/hctk_scalar_partition_regression.lean'], lake=lake),
                                cwd=ROOT, text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_master_registry_projection(self):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake)
        result = subprocess.run(lean_command(['-DwarningAsError=true', 'tests/lean/hctk_scalar_partition_registry.lean'], lake=lake),
                                cwd=ROOT, text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_explicit_three_store_capture(self):
        result = subprocess.run(lean_command(['-DwarningAsError=true', 'tests/lean/hctk_capture_regression.lean'], lake=shutil.which('lake')),
                                cwd=ROOT, text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
