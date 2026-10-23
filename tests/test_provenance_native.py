"""Actual native-FFI conformance. Synthetic failures are explicitly separate.
Fixed KATs/fixture are replayed without fixture generation or signing at test time.
"""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT/'tools/provenance_native'
DATA = ROOT/'tests/data/provenance_native'
spec = importlib.util.spec_from_file_location('provenance_native_build', HERE/'build.py')
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'Enable Lean/FFI execution explicitly')
class ProvenanceNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='provenance-native-')
        cls.directory = Path(cls.temp.name)
        cls.profile = json.loads((HERE/'profile.json').read_text())
        cls.shim = build.build(cls.directory, cls.profile)
        cls.kat = json.loads((DATA/'kat.json').read_text())
        cls.faults = {}
        for name, flags in [('init',['-DFAILURE=1']),('hash',['-DFAILURE=2']),
                            ('result',['-DFAILURE=3']),('size',['-DFAILURE=4']),
                            ('symbol',['-DOMIT_HASH'])]:
            path = cls.directory/(name+'.so')
            subprocess.run(['cc','-std=c11','-Wall','-Wextra','-Werror','-shared','-fPIC',
                            *flags,str(DATA/'failing_backend.c'),'-o',str(path)],check=True)
            cls.faults[name] = str(path)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def lean(self, script, argument):
        # Recheck the external binary before launching. This is not TOCTOU protection.
        build.qualify(self.profile)
        result = subprocess.run(['lake','env','lean','-j1','-DwarningAsError=true',
                                 '--load-dynlib='+str(self.shim),'--run',script,
                                 self.profile['library_path'],self.profile['library_version'],str(argument)],
                                cwd=ROOT,capture_output=True,text=True,timeout=180)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        return result.stdout

    def probe(self, cases):
        path = self.directory/'cases.json'
        path.write_text(json.dumps(cases))
        output = [json.loads(line) for line in self.lean('tests/lean/provenance_native_probe.lean',path).splitlines()]
        self.assertEqual(len(output),len(cases))
        self.assertEqual([x['id'] for x in output],[x['id'] for x in cases])
        for case, actual in zip(cases,output):
            with self.subTest(case=case['id']):
                self.assertEqual(actual['result'],case['expected'])
                if 'digest' in case:
                    self.assertEqual(actual['digest'],case['digest'])
        print('NATIVE_CASES',len(cases),flush=True)
        return output

    def test_rfc8032_positive_known_answers(self):
        self.assertEqual(len(self.kat['ed25519']),5)
        self.probe(self.kat['ed25519'])

    def test_sha256_known_answers_and_block_boundaries(self):
        cases=[dict(x,operation='hash',expected='ok') for x in self.kat['sha256']]
        for n in [0,1,55,56,63,64,65,127,128,129,1024,4096]:
            data=bytes(i % 251 for i in range(n))
            cases.append(dict(id='hash-boundary-'+str(n),operation='hash',message=data.hex(),
                              expected='ok',digest=hashlib.sha256(data).hexdigest()))
        self.probe(cases)

    def test_every_byte_mutation(self):
        original=self.kat['ed25519'][2]
        cases=[]
        for field in ['signature','key','message']:
            data=bytes.fromhex(original[field])
            for index in range(len(data)):
                changed=bytearray(data);changed[index]^=1
                cases.append(dict(original,id=f'mutation-{field}-{index}',expected='ok_false',
                                  **{field:changed.hex()}))
        self.assertEqual(len(cases),98)
        self.probe(cases)

    def test_noncanonical_points_small_order_and_scalar_malleability(self):
        original=self.kat['ed25519'][0]
        sig=bytes.fromhex(original['signature'])
        order=2**252+27742317777372353535851937790883648493
        cases=[]
        points=[('zero',bytes(32)),('identity',b'\x01'+bytes(31)),
                ('p',(2**255-19).to_bytes(32,'little')),('max',bytes([255])*32),
                ('identity-sign',(1+2**255).to_bytes(32,'little'))]
        for name,point in points:
            cases.append(dict(original,id='bad-key-'+name,key=point.hex(),expected='ok_false'))
            cases.append(dict(original,id='bad-R-'+name,signature=(point+sig[32:]).hex(),expected='ok_false'))
        for name,value in [('L',order),('SplusL',int.from_bytes(sig[32:],'little')+order),('max',2**256-1)]:
            cases.append(dict(original,id='bad-S-'+name,signature=(sig[:32]+value.to_bytes(32,'little')).hex(),expected='ok_false'))
        self.probe(cases)

    def test_wrong_lengths_at_lean_and_c_boundaries(self):
        cases=[]
        for op in ['verify','raw_verify']:
            for field,sizes in [('key',[0,1,31,33,64]),('signature',[0,1,63,65,128])]:
                for size in sizes:
                    cases.append(dict(self.kat['ed25519'][0],id=f'{op}-{field}-{size}',operation=op,
                                      expected='backend_failure',**{field:bytes(size).hex()}))
        self.probe(cases)

    def test_loader_initialization_abi_and_runtime_failures(self):
        original=self.kat['ed25519'][0]
        cases=[]
        for name,path in [('missing','/nonexistent/libsodium.so'),*self.faults.items()]:
            # hash failure fixture verifies to false normally, not a backend failure.
            if name != 'hash':
                cases.append(dict(original,id=name+'-verify',library=path,expected='backend_failure'))
            cases.append(dict(id=name+'-hash',operation='hash',message='616263',library=path,expected='backend_failure'))
        cases.append(dict(original,id='wrong-version',version='unqualified',expected='backend_failure'))
        cases.append(dict(original,id='relative-path',library='libsodium.so.23',expected='backend_failure'))
        cases.append(dict(original,id='embedded-nul-path',library=self.profile['library_path']+'\x00other',expected='backend_failure'))
        self.probe(cases)

    def test_full_native_report_and_observed_io_isolation(self):
        output=self.lean('tests/lean/provenance_native_integration.lean',DATA/'integration.json')
        self.assertIn('NATIVE_INTEGRATION_OK ',output)
        print(output.strip(),flush=True)

    def test_pin_rejects_unqualified_binary_without_execution(self):
        profile=copy.deepcopy(self.profile)
        profile['library_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'unqualified'):
            build.qualify(profile)

    def test_qualified_launcher(self):
        result=subprocess.run(['python3',str(HERE/'run.py'),
                               'tests/lean/provenance_native_integration.lean',
                               str(DATA/'integration.json')],cwd=ROOT,capture_output=True,text=True,timeout=180)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('NATIVE_INTEGRATION_OK 28',result.stdout)

    def test_launcher_rejects_wrong_pin(self):
        profile=copy.deepcopy(self.profile);profile['library_sha256']='0'*64
        path=self.directory/'unqualified.json';path.write_text(json.dumps(profile))
        result=subprocess.run(['python3',str(HERE/'run.py'),'--profile',str(path),
                               'tests/lean/provenance_native_integration.lean',str(DATA/'integration.json')],
                              cwd=ROOT,capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,2)
        self.assertIn('unqualified',result.stderr)
        self.assertNotIn('NATIVE_INTEGRATION_OK',result.stdout)

    def test_effects_do_not_enter_proof_graph(self):
        for path in (ROOT/'Verification').rglob('*.lean'):
            self.assertNotIn('provenance_native',path.read_text())
        self.assertNotIn('provenance_native',(ROOT/'Verification.lean').read_text())
        self.assertNotIn('unsafe',(HERE/'Adapter.lean').read_text())
        self.assertNotIn('unsafe',(HERE/'Raw.lean').read_text())


if __name__ == '__main__':
    unittest.main()
