import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from lean_invoke import elaborate_command
from release_evidence import strict_build_command, beta_commands
from inventory_lean_invocations import category


class InvocationTests(unittest.TestCase):
    def test_compiler_flags_follow_separator(self):
        self.assertEqual(elaborate_command('path with spaces.lean', extra_args=['--json']),
                         ['lake', 'lean', 'path with spaces.lean', '--', '-j1',
                          '-DwarningAsError=true', '--json'])

    def test_build_includes_unregistered_and_pilot_sources(self):
        inputs = {'Verification.lean': 'root', 'Verification/A.lean': 'a',
                  'Verification/Specs/Outside.lean': 'b',
                  'Verification/AlgebraicCertificateNormalizeCached.lean': 'c',
                  'tests/lean/example.lean': 'fixture'}
        self.assertEqual(strict_build_command(inputs), [
            'lake', 'build', '--wfail', 'Verification',
            'Verification.A', 'Verification.AlgebraicCertificateNormalizeCached',
            'Verification.Specs.Outside'])

    def test_runtime_queries_are_not_elaboration(self):
        self.assertEqual(category('tools/build.py', "['lean', '--print-prefix']"),
                         'runtime-query-no-elaboration')
        self.assertEqual(category('docs/example.md', 'lake env lean Test.lean'),
                         'documentation-or-comment')
        self.assertEqual(category('tools/reader.lean',
                                  '"Usage: lake env lean --run reader.lean"'),
                         'documentation-or-comment')

    def test_gate_and_ci_use_configured_elaboration(self):
        commands = beta_commands({'Verification/A.lean': 'a'}, '/auditor')
        self.assertEqual(commands[0], ('root-build', strict_build_command(
            {'Verification/A.lean': 'a'})))
        self.assertEqual(dict(commands)['registry-audit'],
                         elaborate_command('Verification/AxiomAudit.lean'))
        self.assertLess([n for n, _ in commands].index('root-build'),
                        [n for n, _ in commands].index('independent-audit'))
        workflow = (ROOT / '.github/workflows/lean_action_ci.yml').read_text()
        self.assertIn('python3 tools/lean_invoke.py '
                      'Verification/Specs/QuantumQutritDecoderSpec.lean', workflow)

    @unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS'), 'live Lean opt-in')
    def test_explicit_build_detects_bad_unregistered_module(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'lean-toolchain').write_bytes((ROOT / 'lean-toolchain').read_bytes())
            (root / 'lakefile.toml').write_text(
                'name = "coverage_probe"\n[[lean_lib]]\nname = "Verification"\n')
            (root / 'Verification').mkdir()
            (root / 'Verification.lean').write_text('import Verification.A\n')
            (root / 'Verification/A.lean').write_text('def a : Nat := 1\n')
            outside = root / 'Verification/Outside.lean'
            outside.write_text('def outside : Nat := missingCoverageProbe\n')
            inputs = {str(p.relative_to(root)): '' for p in root.rglob('*.lean')}
            baseline = subprocess.run(['lake', 'build', 'Verification', '--wfail'],
                                      cwd=root, capture_output=True, text=True, timeout=60)
            self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
            checked = subprocess.run(strict_build_command(inputs), cwd=root,
                                     capture_output=True, text=True, timeout=60)
            self.assertNotEqual(checked.returncode, 0)
            self.assertIn('missingCoverageProbe', checked.stdout + checked.stderr)
            outside.write_text('def outside : Nat := 2\n')
            fixed = subprocess.run(strict_build_command(inputs), cwd=root,
                                   capture_output=True, text=True, timeout=60)
            self.assertEqual(fixed.returncode, 0, fixed.stdout + fixed.stderr)

    @unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS'), 'live Lean opt-in')
    def test_workspace_options_enforced_with_negative_control(self):
        # Tiny dependency-free Lake project: no shared project artifacts reused.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'lean-toolchain').write_bytes((ROOT / 'lean-toolchain').read_bytes())
            (root / 'lakefile.toml').write_text(
                'name = "option_probe"\n[leanOptions]\n'
                'autoImplicit = false\nwarningAsError = true\n')
            path = root / 'Probe.lean'
            path.write_text('def identityProbe (x : MissingType) := x\n')
            bare = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root,
                                  capture_output=True, text=True, timeout=60)
            self.assertEqual(bare.returncode, 0, bare.stdout + bare.stderr)
            strict = subprocess.run(elaborate_command(path), cwd=root,
                                    capture_output=True, text=True, timeout=60)
            self.assertNotEqual(strict.returncode, 0)
            self.assertIn('MissingType', strict.stdout + strict.stderr)
            self.assertIn('Unknown identifier', strict.stdout + strict.stderr)
            path.write_text('def identityProbe (x : Nat) := x\n')
            good = subprocess.run(elaborate_command(path), cwd=root,
                                  capture_output=True, text=True, timeout=60)
            self.assertEqual(good.returncode, 0, good.stdout + good.stderr)


if __name__ == '__main__':
    unittest.main()
