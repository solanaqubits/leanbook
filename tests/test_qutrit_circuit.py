"""Kernel and registry checks for Qutrit gate circuit refinement."""
from tools.lean_invoke import lean_command
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class QutritCircuitLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(lean_command(['-DwarningAsError=true', file], lake=lake),
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_qutrit_circuit_contract(self):
        # The pinned test specification is outside the default library import
        # closure. Build it explicitly instead of relying on another test's cache.
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        build = subprocess.run(
            [lake, 'build', '--wfail', 'Verification.Specs.QuantumQutritDecoderSpec'],
            cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
        self.run_lean('tests/lean/qutrit_circuit_regression.lean')

    def test_executable_basis_interpreter(self):
        result = subprocess.run(lean_command(['-DwarningAsError=true', '--run', 'tests/lean/qutrit_circuit_execution.lean'], lake=shutil.which('lake')),
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.strip(), '0,5,7,8,1,3,4,6,2')

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/qutrit_circuit_registry.lean')


if __name__ == '__main__':
    unittest.main()
