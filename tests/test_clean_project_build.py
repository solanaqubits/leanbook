import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from clean_project_build import (clean_project, dependency_state, project_plan,
                                 run, validate_receipt, check_coverage)
from clean_build_container import launch


class CleanBuildTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name); self.root = self.base / 'repo'; self.root.mkdir()
        subprocess.run(['git', 'init', '-q'], cwd=self.root, check=True)
        (self.root / '.gitignore').write_text('.lake/\n')
        (self.root / 'lakefile.toml').write_text(
            'name="clean_probe"\n[[lean_lib]]\nname="Verification"\n'
            '[[lean_exe]]\nname="probe"\nroot="Main"\n')
        (self.root / 'lean-toolchain').write_bytes((ROOT / 'lean-toolchain').read_bytes())
        (self.root / 'lake-manifest.json').write_text(
            '{"version":"1.2.0","packagesDir":".lake/packages","packages":[],"name":"clean_probe","lakeDir":".lake"}')
        (self.root / 'Verification').mkdir()
        (self.root / 'Verification.lean').write_text('import Verification.A\n')
        (self.root / 'Verification/A.lean').write_text('def probeA : Nat := 1\n')
        (self.root / 'Verification/Outside.lean').write_text('def outside : Nat := 2\n')
        (self.root / 'Main.lean').write_text('def main : IO Unit := IO.println "probe"\n')

    def test_plan_includes_outside_root_and_executable(self):
        p = project_plan(self.root)
        self.assertEqual(p['modules'], ['Main', 'Verification', 'Verification.A', 'Verification.Outside'])
        self.assertEqual(p['executables'], {'probe': 'Main'})

    def test_clean_removes_all_project_kinds_and_preserves_packages(self):
        build = self.root / '.lake/build'
        for name in ('lib/lean/Verification/A.olean', 'lib/lean/Verification/A.trace',
                     'ir/Main.c.o', 'bin/probe', 'unexpected-cache.hash'):
            p = build / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_text('old')
        package = self.root / '.lake/packages/dep/.lake/build/test.olean'
        package.parent.mkdir(parents=True); package.write_text('preserve')
        clean_project(self.root)
        self.assertEqual(list(build.iterdir()), [])
        self.assertEqual(package.read_text(), 'preserve')

    def test_symlinked_build_refused(self):
        outside = self.base / 'outside'; outside.mkdir(); (outside / 'keep').write_text('safe')
        (self.root / '.lake').mkdir(); (self.root / '.lake/build').symlink_to(outside)
        with self.assertRaises(ValueError): clean_project(self.root)
        self.assertEqual((outside / 'keep').read_text(), 'safe')

    def test_custom_layout_refused(self):
        with (self.root / 'lakefile.toml').open('w') as f:
            f.write('name="x"\nbuildDir="elsewhere"\n')
        with self.assertRaises(ValueError): project_plan(self.root)

    def test_writable_dependency_refused(self):
        p = self.root / '.lake/packages/pkg'; p.mkdir(parents=True)
        (self.root / 'lake-manifest.json').write_text('{"packages":[{"name":"pkg"}]}')
        with self.assertRaisesRegex(ValueError, 'read-only'): dependency_state(self.root)

    def test_partial_fresh_count_is_not_coverage(self):
        with self.assertRaisesRegex(ValueError, 'coverage'):
            check_coverage(self.root, project_plan(self.root),
                           '✔ [1/4] Built Verification.A (1s)\n', 0)

    def test_post_build_allows_only_explicit_auxiliary_modules(self):
        plan = project_plan(self.root)
        build = self.root / '.lake/build'
        log = ''
        for i, module in enumerate(plan['modules']):
            log += f'✔ [{i+1}/4] Built {module} (1s)\n'
            stem = module.replace('.', '/')
            for name in [f'lib/lean/{stem}{suffix}' for suffix in ('.olean', '.ilean', '.trace')] + [f'ir/{stem}.c']:
                p = build / name; p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text('{"synthetic":false,"depHash":"fresh"}' if name.endswith('.trace') else 'fresh')
        binary = build / 'bin/probe'; binary.parent.mkdir(parents=True); binary.write_text('binary')
        aux = build / 'lib/lean/tools/challenge_store/Wire.olean'
        aux.parent.mkdir(parents=True); aux.write_text('auxiliary')
        with self.assertRaisesRegex(ValueError, 'olean set'):
            check_coverage(self.root, plan, log, 0)
        check_coverage(self.root, plan, log, 0, auxiliary_modules=['tools.challenge_store.Wire'])
        unexpected = build / 'lib/lean/Verification/Unexpected.olean'; unexpected.write_text('stale')
        with self.assertRaisesRegex(ValueError, 'olean set'):
            check_coverage(self.root, plan, log, 0, auxiliary_modules=['tools.challenge_store.Wire'])
        unexpected.unlink()
        (build / 'lib/lean/Verification/A.olean').unlink()
        with self.assertRaisesRegex(ValueError, 'olean set'):
            check_coverage(self.root, plan, log, 0, auxiliary_modules=['tools.challenge_store.Wire'])

    def test_container_mounts_and_cleanup(self):
        out = self.base / 'container'
        def output(cmd, **kwargs):
            return '/toolchain\n' if cmd[0] == 'lake' else str(self.root / '.git') + '\n'
        with patch('clean_build_container.subprocess.check_output', side_effect=output), \
             patch('clean_build_container.subprocess.run', return_value=SimpleNamespace(stdout='0\n')) as spawn:
            self.assertEqual(launch(self.root, out, 'sha256:' + 'a'*64)['status'], 'passed')
        commands = [x.args[0] for x in spawn.call_args_list]
        docker_run = next(c for c in commands if c[:2] == ['docker', 'run'])
        self.assertIn('--network=none', docker_run)
        self.assertIn('--memory=12g', docker_run)
        self.assertIn('/toolchain:/toolchain:ro', docker_run)
        self.assertTrue(any(c[:3] == ['docker', 'rm', '-f'] for c in commands))

    def test_outer_timeout_kills_owned_container(self):
        out = self.base / 'container'
        def output(cmd, **kwargs):
            return '/toolchain\n' if cmd[0] == 'lake' else str(self.root / '.git') + '\n'
        def execute(cmd, **kwargs):
            if cmd[:2] == ['docker', 'wait']:
                raise subprocess.TimeoutExpired(cmd, 3700)
            return SimpleNamespace(stdout='')
        with patch('clean_build_container.subprocess.check_output', side_effect=output), \
             patch('clean_build_container.subprocess.run', side_effect=execute) as spawn:
            with self.assertRaises(RuntimeError): launch(self.root, out, 'sha256:' + 'a'*64)
        commands = [x.args[0] for x in spawn.call_args_list]
        self.assertTrue(any(c[:2] == ['docker', 'kill'] for c in commands))
        self.assertTrue(json.loads((out / 'status.json').read_text())['timeout'])

    @unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS'), 'live Lean opt-in')
    def test_live_clean_graph_and_receipt_tampering(self):
        # Seed all caches, then prove that run() invalidates every project artifact.
        initial = subprocess.run(['lake', 'build', 'Verification', 'probe'], cwd=self.root,
                                 capture_output=True, text=True, timeout=60)
        self.assertEqual(initial.returncode, 0, initial.stdout + initial.stderr)
        extra = self.root / '.lake/build/old-unregistered.olean'; extra.write_text('stale')
        out = self.base / 'evidence'
        r = run(self.root, out, timeout=60)
        self.assertFalse(extra.exists())
        self.assertEqual(r['coverage']['fresh_module_count'], 4)
        self.assertEqual(r['reused_dependency_package_count'], 0)
        self.assertEqual(validate_receipt(self.root, out)['status'], 'passed')
        r['coverage']['fresh_modules'].pop()
        (out / 'receipt.json').write_text(json.dumps(r))
        with self.assertRaises(ValueError): validate_receipt(self.root, out)

    @unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS'), 'live Lean opt-in')
    def test_live_native_helpers_preserve_frozen_receipt(self):
        out = self.base / 'native-evidence'
        receipt = run(self.root, out, timeout=60)
        # Structural regression for the five outputs observed in the full native
        # beta. Compiler/runtime correctness is checked by the native test suite.
        for module in ('tools.challenge_store.Wire', 'tools.challenge_store.FileManifest',
                       'tools.challenge_store.Worker', 'tools.provenance_native.Raw',
                       'tools.provenance_native.Adapter'):
            path = self.root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
            path.parent.mkdir(parents=True, exist_ok=True); path.write_text('native helper')
        self.assertEqual(validate_receipt(self.root, out)['status'], 'passed')
        frozen = self.root / '.lake/build/lib/lean/Verification/A.olean'
        frozen.write_bytes(frozen.read_bytes() + b'tampering')
        with self.assertRaisesRegex(ValueError, 'project artifact changed'):
            validate_receipt(self.root, out)
        self.assertEqual(receipt['coverage']['fresh_module_count'], 4)

    @unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS'), 'live Lean opt-in')
    def test_failed_build_keeps_failure_receipt(self):
        (self.root / 'Verification/Outside.lean').write_text('def broken := unknownIdentifier\n')
        out = self.base / 'evidence'
        with self.assertRaisesRegex(ValueError, 'strict build failed'):
            run(self.root, out, timeout=60)
        r = json.loads((out / 'receipt.json').read_text())
        self.assertEqual(r['status'], 'failed')
        self.assertNotEqual(r['exit_code'], 0)


if __name__ == '__main__': unittest.main()
