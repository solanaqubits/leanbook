"""Live boundary and registry checks for the bounded Cairo block model."""
from tools.lean_invoke import elaborate_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for kernel checks')
class MlDsaCairoLiveTests(unittest.TestCase):
    def check_fixture(self, name):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(elaborate_command(f'tests/lean/{name}.lean', lake=lake),
                                cwd=ROOT, text=True, capture_output=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_mldsa_rt1_boundaries(self):
        self.check_fixture('mldsa_rt1_boundaries')

    def test_mldsa_u128_conversion_boundaries(self):
        self.check_fixture('mldsa_u128_conversion_boundaries')

    def test_mldsa_production_conversion_block_boundaries(self):
        self.check_fixture('mldsa_production_conversion_block_boundaries')

    def test_mldsa_cairo_registry(self):
        self.check_fixture('mldsa_cairo_registry')


    def test_stage20_registry_contract(self):
        self.check_fixture('mldsa_stage20_registry')
