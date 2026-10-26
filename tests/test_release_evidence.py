import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from release_evidence import digest, snapshot, validate_report, AUDITOR_SHA


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        mock=patch("release_evidence.runtime_fingerprint",return_value={"test_runtime":1});mock.start();self.addCleanup(mock.stop)
        clean = patch('release_evidence.validate_clean_receipt', return_value={
            'coverage': {'fresh_modules': ['Verification', 'Verification.A']},
            'reused_dependency_packages': []})
        clean.start(); self.addCleanup(clean.stop)
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)/'repo';self.root.mkdir()
        subprocess.run(['git','init','-q'],cwd=self.root,check=True)
        (self.root/'Verification').mkdir();(self.root/'Verification/A.lean').write_text('theorem yes : True := True.intro\n')
        (self.root/'Verification.lean').write_text('import Verification.A\n')
        self.out=Path(self.tmp.name)/'evidence';self.out.mkdir()
        inputs=snapshot(self.root)
        logs={'root-build':'Build completed successfully (3 jobs).\n',
              'verify-all':json.dumps(dict(ok=True,source_unchanged=True,policy_findings=[],modules=['Verification.A'],source_sha256={'Verification.A':inputs['Verification/A.lean']},audit={'axioms':[],'declarations':1,'violations':[]})),
              'independent-audit':json.dumps(dict(ok=True,violations=[],audited=1,axiomsUsed=[])),
              'all-tests':'Ran 1 tests in 0.1s\n\nOK\n',
              'native-build':'passed','registry-audit':'passed','knowledge':'passed','scope':'{}','diff':''}
        (self.out/'clean-project').mkdir()
        (self.out/'clean-project/receipt.json').write_text('{}')
        (self.out/'clean-project/build.log').write_text(logs['root-build'])
        self.report=dict(schema_version=3,rank='beta',status='passed',inputs=inputs,checks=[],auditor_sha256=AUDITOR_SHA,runtime={'test_runtime':1}, clean_project_receipt_sha256=digest(self.out/'clean-project/receipt.json'))
        for n,text in logs.items():
            p=self.out/(n+'.log');p.write_text(text)
            self.report['checks'].append(dict(name=n,exit_code=0,log=p.name,log_sha256=digest(p)))
        self.save()
    def save(self):
        (self.out/'evidence.json').write_text(json.dumps(self.report))
    def test_consistent_evidence(self):
        self.assertTrue(validate_report(self.root,self.out)['ok'])
    def test_native_build_required_before_tests(self):
        from release_evidence import beta_commands
        commands = beta_commands({}, '/auditor', self.out)
        names = [n for n, _ in commands]
        self.assertLess(names.index('native-build'), names.index('all-tests'))
        self.assertEqual(dict(commands)['native-build'],
                         ['python3', '-m', 'tools.challenge_store.build'])
        self.report['checks'] = [c for c in self.report['checks'] if c['name'] != 'native-build']
        self.save()
        with self.assertRaises(ValueError): validate_report(self.root, self.out)

    def test_runtime_change_rejected(self):
        self.report['runtime'] = {'test_runtime':2};self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_legacy_cached_gate_is_not_new_beta(self):
        self.report['schema_version'] = 1; self.save()
        with self.assertRaises(ValueError): validate_report(self.root,self.out)
    def test_missing_clean_receipt_pin_rejected(self):
        del self.report['clean_project_receipt_sha256']; self.save()
        with self.assertRaises(ValueError): validate_report(self.root,self.out)
    def test_clean_receipt_validator_failure_propagates(self):
        with patch('release_evidence.validate_clean_receipt', side_effect=ValueError('cached graph')):
            with self.assertRaisesRegex(ValueError, 'cached graph'):
                validate_report(self.root,self.out)
    def test_failed_check_rejected(self):
        self.report['checks'][0]['exit_code']=1;self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_tree_change_rejected(self):
        (self.root/'Verification/A.lean').write_text('-- changed\n')
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_log_change_rejected(self):
        (self.out/'all-tests.log').write_text('OK\n')
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_missing_check_rejected(self):
        self.report['checks'].pop();self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_wrong_digest_rejected(self):
        with self.assertRaises(ValueError):validate_report(self.root,self.out,'0'*64)
    def test_skip_rejected_even_with_updated_hash(self):
        p=self.out/'all-tests.log';p.write_text('Ran 1 tests in 0.1s\nOK (skipped=1)\n')
        next(c for c in self.report['checks'] if c['name']=='all-tests')['log_sha256']=digest(p);self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_incomplete_source_coverage_rejected(self):
        p=self.out/'verify-all.log';v=json.loads(p.read_text());v['modules']=[];p.write_text(json.dumps(v))
        next(c for c in self.report['checks'] if c['name']=='verify-all')['log_sha256']=digest(p);self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)

if __name__=='__main__':unittest.main()
