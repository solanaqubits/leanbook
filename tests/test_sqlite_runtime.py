"""Runtime adoption: pinned loader and historical v1 checkpoint continuity.

Synthetic databases only; no production Witness or application rollout assertion.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from tools.challenge_store import runtime

ROOT = Path(__file__).resolve().parents[1]
LEGACY = ROOT / 'tests/data/sqlite_runtime_legacy.json'
PROFILE = ROOT / 'tools/challenge_store/checkpoint_profile_v1.json'


class RuntimePackagingTests(unittest.TestCase):
    def setUp(self):
        # Installer deliberately rejects writable ancestors (including /tmp).
        self.temp = tempfile.TemporaryDirectory(dir=Path.home())
        self.root = Path(self.temp.name)
        self.source = self.root / 'qualified.so'
        self.source.write_bytes(b'synthetic qualified bytes; never loaded')
        self.target = self.root / 'isolated' / 'version' / 'libsqlite3.so.0.8.6'
        self.p = dict(library_path=str(self.target),
                      library_sha256=hashlib.sha256(self.source.read_bytes()).hexdigest())
        self.mock = patch.object(runtime, 'profile', return_value=self.p)
        self.mock.start()

    def tearDown(self):
        self.mock.stop()
        self.temp.cleanup()

    def test_exclusive_install_and_idempotent_existing_install(self):
        self.assertEqual(runtime.install(self.source), self.target)
        before = self.target.stat().st_mtime_ns
        runtime.install(self.source)
        self.assertEqual(before, self.target.stat().st_mtime_ns)
        self.assertEqual(runtime.verified_library(), self.target)
        self.assertEqual(self.target.parent.stat().st_mode & 0o777, 0o700)

    def test_wrong_source_never_creates_destination(self):
        self.source.write_bytes(b'wrong')
        with self.assertRaises(ValueError): runtime.install(self.source)
        self.assertFalse(self.target.parent.exists())

    def test_existing_wrong_file_not_overwritten(self):
        self.target.parent.mkdir(parents=True)
        self.target.write_bytes(b'existing')
        with self.assertRaises(ValueError): runtime.install(self.source)
        self.assertEqual(self.target.read_bytes(), b'existing')

    def test_tampering_permissions_alias_and_extra_library_refused(self):
        runtime.install(self.source)
        alias = self.target.parent / 'libsqlite3.so.0'
        self.target.chmod(0o520)
        with self.assertRaises(ValueError): runtime.verified_library()
        self.target.chmod(0o500)
        alias.unlink(); alias.symlink_to(self.source)
        with self.assertRaises(ValueError): runtime.verified_library()
        alias.unlink(); alias.symlink_to(self.target.name)
        extra = self.target.parent / 'unexpected.so'; extra.touch()
        with self.assertRaises(ValueError): runtime.verified_library()
        extra.unlink(); self.target.chmod(0o700); self.target.write_bytes(b'tampered')
        with self.assertRaises(ValueError): runtime.verified_library()

    def test_loader_injection_refused_and_path_not_appended(self):
        runtime.install(self.source)
        for key in ('LD_PRELOAD', 'LD_AUDIT'):
            with patch.dict(os.environ, {key: '/unexpected.so'}):
                with self.assertRaises(ValueError): runtime.environment()
        with patch.dict(os.environ, {'LD_LIBRARY_PATH': '/untrusted', 'LD_PRELOAD': '', 'LD_AUDIT': ''}):
            self.assertEqual(runtime.environment()['LD_LIBRARY_PATH'], str(self.target.parent))

    def test_missing_runtime_does_not_use_system_fallback(self):
        with self.assertRaises(ValueError): runtime.environment()
        self.assertFalse(self.target.exists())


@unittest.skipUnless(os.environ.get('PROVENANCE_STORE_LIVE_TESTS') == '1', 'Enable native runtime checks')
class RuntimeContinuityTests(unittest.TestCase):
    def child(self, code, args=(), env=None):
        result = subprocess.run([sys.executable, '-c', code, *map(str,args)],
                                cwd=ROOT, env=env, capture_output=True, text=True, timeout=90)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_actual_mapped_library_and_frozen_profile(self):
        from tools.challenge_store.store import qualify_sqlite
        qualify_sqlite()
        self.assertEqual(hashlib.sha256(PROFILE.read_bytes()).hexdigest(),
                         '93c065d0816809ed39f5432c24b0947dd8db624e55a506c3d7a37aba391d2583')
        self.assertNotEqual(runtime.profile()['library_sha256'], json.loads(PROFILE.read_text())['library_sha256'])

    def test_direct_system_runtime_refused_before_creating_database(self):
        env = dict(os.environ)
        for key in ('LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'): env.pop(key, None)
        with tempfile.TemporaryDirectory() as t:
            path = Path(t) / 'must-not-exist.db'
            self.child('''
import sys
from tools.challenge_store.store import Store,Controller,StoreError
try: Store.initialize(sys.argv[1],Controller())
except StoreError as e: assert e.code=='unqualified_configuration'
else: raise AssertionError('System runtime unexpectedly accepted')
''', [path], env)
            self.assertFalse(path.exists())

    def test_launcher_check_and_cli_error_use_new_interpreter(self):
        env = dict(os.environ)
        for key in ('LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'): env.pop(key, None)
        p = subprocess.run([sys.executable, '-m', 'tools.challenge_store.runtime', 'check'],
                           cwd=ROOT,env=env,capture_output=True,text=True,timeout=20)
        self.assertEqual(p.returncode,0,p.stderr)
        out=json.loads(p.stdout);self.assertEqual(out['status'],'runtime_verified')
        self.assertEqual(out['library_sha256'],runtime.profile()['library_sha256'])
        self.assertEqual(out['authorization'],'blocked')
        p = subprocess.run([sys.executable, '-m', 'tools.challenge_store.runtime', 'run', '--', '--bad-flag'],
                           cwd=ROOT,env=env,capture_output=True,text=True,timeout=20)
        self.assertEqual(p.returncode,2);self.assertIn('anchored_cli',p.stderr)

    def test_legacy_database_head_read_submit_resolve_and_retry(self):
        from tools.challenge_store.store import Store
        from tools.challenge_store.anchor import AnchoredStore,Ready,checkpoint_digest
        from tools.challenge_store.files import submit_files
        from tests.test_provenance_anchor import TestWitness
        from tests.test_provenance_files import expected,key_of,package,sql_state
        fixed=json.loads(LEGACY.read_text()); identity='runtime-continuity-v1'
        with tempfile.TemporaryDirectory() as t:
            db=Path(t)/'legacy.db'
            # Original system SQLite creates the old issued schema/image, without
            # loading new Store or touching an existing database.
            env=dict(os.environ)
            for key in ('LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
            self.child('''
import hashlib,json,sqlite3,sys
from pathlib import Path
assert sqlite3.sqlite_version=='3.45.1'
p=json.loads(Path('tools/challenge_store/checkpoint_profile_v1.json').read_text())
mapped={line.split()[-1] for line in Path('/proc/self/maps').read_text().splitlines() if '/libsqlite3.so' in line}
assert mapped=={p['library_path']}
assert hashlib.sha256(Path(p['library_path']).read_bytes()).hexdigest()==p['library_sha256']
db=sqlite3.connect(sys.argv[1]);db.execute('PRAGMA journal_mode=WAL');db.execute('PRAGMA foreign_keys=ON')
db.executescript(Path('tools/challenge_store/schema.sql').read_text())
fixed=json.loads(Path(sys.argv[2]).read_text())
for table in ('context_versions','active_contexts','challenge_entries','transactions'):
 for row in fixed['sql'][table]:
  values=[bytes.fromhex(v['blob_hex']) if isinstance(v,dict) else v for v in row]
  db.execute('INSERT INTO '+table+' VALUES ('+','.join('?' for _ in row)+')',values)
db.commit();db.close()
''',[db,LEGACY],env)
            head=Ready(**fixed['head']);w=TestWitness();w.provision(identity,head)
            with AnchoredStore(db,store_id=identity,witness=w) as s:
                image=s.inspect();self.assertEqual(image,fixed['image'])
                self.assertEqual(checkpoint_digest(identity,image),head.digest)
                self.assertEqual(w.writes,0)
                out=submit_files(s,'runtime-first','v1',package())
                self.assertIn('newly_consumed',out['redemption']['result'])
            self.assertGreater(w.read(identity).epoch,head.epoch)
            with AnchoredStore(db,store_id=identity,witness=w) as s:
                self.assertIn('confirmed_committed',s.resolve(key_of(expected()['context']),'runtime-first')['resolution']['result'])
                before=sql_state(s); count=w.writes
                self.assertIn('idempotent_replay_matched',submit_files(s,'runtime-first','v1',package())['redemption']['result'])
                self.assertEqual(sql_state(s),before);self.assertEqual(w.writes,count)
                self.assertIn('idempotent_replay_matched',submit_files(s,'runtime-history','v1',package())['redemption']['result'])
                self.assertEqual(s.db.execute("SELECT acceptance_kind FROM transactions WHERE tx_id='runtime-history'").fetchone(),('historicalReturn',))
                self.assertEqual(s.db.execute('PRAGMA integrity_check').fetchone(),('ok',))
