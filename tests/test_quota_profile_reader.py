"""Bounded reader IO tests; no assertion of formal OS or memory-cost verification."""
from tools.lean_invoke import lean_command
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
READER = ROOT / 'tools/quota_profile_reader.lean'


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class QuotaProfileReaderLiveTests(unittest.TestCase):
    def lean(self, *args):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        return subprocess.run(lean_command(['-DwarningAsError=true', *map(str, args)], lake=lake),
                              cwd=ROOT, capture_output=True, text=True, timeout=120)

    def cli(self, path, size='64', count='3'):
        result = self.lean('--run', READER, path, size, count)
        self.assertIn(result.returncode, (0, 2), result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report['authorization'], 'blocked')
        self.assertEqual(result.returncode, 0 if report['status'] == 'decoded' else 2)
        return report

    def test_callback_short_reads_limits_and_faults(self):
        with tempfile.TemporaryDirectory() as td:
            probe = Path(td) / 'ReaderProbe.lean'
            # Exact source including original main; compilation #eval runs only the appended tests.
            probe.write_text(READER.read_text() + '\n' +
                             (ROOT / 'tests/lean/quota_profile_reader_cases.lean').read_text())
            result = self.lean(probe)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('QUOTA_PROFILE_READER_OK 55', result.stdout)

    def test_file_exact_limit_and_preserved_source(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / 'profile.qcp'
            # Independent fixed v1 bytes: coefficient list [0, 1/2, -2/3].
            data = bytes.fromhex('5143500103000001000102010203')
            path.write_bytes(data)
            before = hashlib.sha256(path.read_bytes()).hexdigest()
            report = self.cli(path, str(len(data)))
            self.assertEqual(report, dict(status='decoded', bytes_read=len(data), coefficient_count=3, format='QCP/01',
                                         expected_context='not_checked', mathematical_restoration='not_run',
                                         provenance='not_verified', authorization='blocked'))
            self.assertEqual(self.cli(path, str(len(data)-1))['status'], 'resource_limit')
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), before)

    def test_empty_and_trailing_files(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / 'profile.qcp'
            path.write_bytes(b'')
            self.assertEqual(self.cli(path, '0')['status'], 'invalid_input')
            path.write_bytes(bytes.fromhex('5143500100'))
            self.assertEqual(self.cli(path, '5', '0')['status'], 'decoded')
            path.write_bytes(bytes.fromhex('514350010000'))
            self.assertEqual(self.cli(path, '6', '0')['status'], 'invalid_input')
            self.assertEqual(self.cli(path, '5', '0')['status'], 'resource_limit')

    def test_os_open_and_read_errors(self):
        with tempfile.TemporaryDirectory() as td:
            self.assertEqual(self.cli(Path(td) / 'absent')['status'], 'io_error')
            self.assertEqual(self.cli(Path(td))['status'], 'io_error')

    def test_cli_limits_before_open(self):
        for size in ('-1', 'not-a-number', '9'*21, str(64*1024*1024+1)):
            with self.subTest(size=size):
                report = self.cli('/nonexistent/quota-reader-test', size)
                self.assertIn(report['status'], ('invalid_arguments', 'invalid_limits'))

    def test_format_and_count_refusals(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / 'profile.qcp'
            for data in ('5143500101000001', '514350018000',
                         '5143500101010001', '5143500101000204',
                         '514353010000', '5143500200', '5143500180'):
                path.write_bytes(bytes.fromhex(data))
                if data == '5143500101000001':
                    self.assertEqual(self.cli(path, count='0')['status'], 'invalid_input')
                    self.assertEqual(self.cli(path, count='1')['status'], 'decoded')
                else:
                    self.assertEqual(self.cli(path)['status'], 'invalid_input')
            for count in ('-1', 'x', '9'*21):
                self.assertEqual(self.cli(path, count=count)['status'], 'invalid_arguments')

    def test_expected_file_api(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / 'profile.qcp'
            path.write_bytes(bytes.fromhex('5143500101000102'))
            probe = Path(td) / 'ExpectedFile.lean'
            code = """
#eval do
  let path : System.FilePath := PATH
  let limits : CryptoHiddenScalarQuotaProfileCodecContract.ProfileLimits := ⟨8, 1⟩
  match ← QuotaProfileReader.readExpectedProfileFile path limits 1 (fun _ => 1/2) with
  | .ok x => unless x.coefficients == [1/2] do throw (IO.userError "bad result")
  | .error e => throw (IO.userError s!"unexpected {repr e}")
  match ← QuotaProfileReader.readExpectedProfileFile path limits 1 (fun _ => 0) with
  | .error .contextMismatch => pure ()
  | _ => throw (IO.userError "wrong context accepted")
  match ← QuotaProfileReader.readExpectedProfileFile (path.toString ++ ".missing")
      limits 1 (fun _ => 1/2) with
  | .error (.ioError "open" _) => pure ()
  | _ => throw (IO.userError "missing file accepted")
  IO.println "EXPECTED_FILE_OK"
""".replace('PATH', json.dumps(str(path)))
            probe.write_text(READER.read_text() + '\n' + code)
            result = self.lean(probe)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('EXPECTED_FILE_OK', result.stdout)

    def test_usage(self):
        result = self.lean('--run', READER)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn('Usage:', result.stderr)


if __name__ == '__main__':
    unittest.main()
