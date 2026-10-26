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
        commands = beta_commands({'Verification/A.lean': 'a'}, '/auditor', '/evidence')
        self.assertEqual(commands[0], ('root-build', ['python3',
            'tools/clean_project_build.py', '--output', '/evidence/clean-project']))
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


class MigratedInvocationTests(unittest.TestCase):
    def test_output_and_runtime_argument_boundaries(self):
        from tools.lean_invoke import lean_command
        cmd=lean_command(['-o','output file.olean','-c','out.c','Test.lean'])
        self.assertEqual(cmd,elaborate_command('Test.lean',extra_args=['-o','output file.olean','-c','out.c']))
        cmd=lean_command(['--load-dynlib=/a b/library.so','--run','Test.lean','--flag','two words'])
        self.assertEqual(cmd,elaborate_command('Test.lean',extra_args=['--load-dynlib=/a b/library.so','--run','Test.lean','--flag','two words']))

    def test_unreviewed_options_and_weakening_refused(self):
        from tools.lean_invoke import lean_command
        for args in [[],['--run'],['-o'],['--unknown','A.lean'],['-DwarningAsError=false','A.lean'],['A.lean','argument']]:
            with self.subTest(args=args), self.assertRaises(ValueError):lean_command(args)

    def test_no_unconfigured_compilation_lists(self):
        import ast
        allowed={('tests/test_lean_invoke.py','test_workspace_options_enforced_with_negative_control'),
                 ('tools/clean_build_container.py','launch')}
        seen=[]
        for folder in ['tests','tools','scripts']:
            for path in (ROOT/folder).rglob('*.py'):
                tree=ast.parse(path.read_text());parents={c:n for n in ast.walk(tree) for c in ast.iter_child_nodes(n)}
                for n in ast.walk(tree):
                    if isinstance(n,ast.List) and len(n.elts)>=3 and [getattr(x,'value',None) for x in n.elts[1:3]]==['env','lean']:
                        if any(getattr(x,'value',None) in ('--version','--print-prefix') for x in n.elts):continue
                        owner=n
                        while owner in parents and not isinstance(owner,ast.FunctionDef):owner=parents[owner]
                        key=(str(path.relative_to(ROOT)),getattr(owner,'name',''))
                        self.assertIn(key,allowed);seen.append(key)
        self.assertEqual(seen,[('tests/test_lean_invoke.py','test_workspace_options_enforced_with_negative_control')])

    @unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS'), 'live Lean opt-in')
    def test_real_run_and_artifact_output_under_project_options(self):
        from tools.lean_invoke import lean_command
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
            (root/'lakefile.toml').write_text('name = "run_option_probe"\n[leanOptions]\nautoImplicit = false\n')
            p=root/'Main.lean';p.write_text('def main (args : List String) : IO Unit := IO.println (repr args)\n')
            r=subprocess.run(lean_command(['--run',str(p),'space value','--literal']),cwd=root,text=True,capture_output=True,timeout=60)
            self.assertEqual(r.returncode,0,r.stdout+r.stderr)
            self.assertEqual(r.stdout.strip(),'["space value", "--literal"]')
            r=subprocess.run(lean_command(['-o',str(root/'out.olean'),'-c',str(root/'out.c'),str(p)]),cwd=root,text=True,capture_output=True,timeout=60)
            self.assertEqual(r.returncode,0,r.stdout+r.stderr)
            self.assertTrue((root/'out.olean').is_file());self.assertTrue((root/'out.c').is_file())

    @unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS'), 'live Lean opt-in')
    def test_distinguish_expected_rejection_from_unrelated_errors(self):
        import json
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
            (root/'lakefile.toml').write_text('name = "negative_probe"\n')
            p=root/'Probe.lean'
            variants=[('example : (0 : Nat) = 0 := by rfl\n',None),
                      ('example : (0 : Nat) = 1 := by rfl\n','rfl'),
                      ('example : Nat := unknownSentinel\n','Unknown identifier'),
                      ('example : Nat := )\n','unexpected token'),
                      ('import AbsentSentinel\n', 'unknown module'),
                      ('def warningProbe (unused : Nat) : Nat := 1\n','not explicitly referenced')]
            for text,expected in variants:
                p.write_text(text)
                r=subprocess.run(elaborate_command(p,extra_args=['--json']),cwd=root,text=True,capture_output=True,timeout=60)
                if expected is None:self.assertEqual(r.returncode,0,r.stdout+r.stderr);continue
                self.assertNotEqual(r.returncode,0)
                if expected=='unknown module':self.assertIn('AbsentSentinel',r.stdout+r.stderr);continue
                errors=[]
                for line in r.stdout.splitlines():
                    try:m=json.loads(line)
                    except ValueError:continue
                    if m.get('severity')=='error':errors.append(m['data'])
                self.assertTrue(errors,r.stdout+r.stderr)
                self.assertTrue(all(expected.lower() in e.lower() for e in errors), errors)

if __name__ == '__main__':
    unittest.main()
