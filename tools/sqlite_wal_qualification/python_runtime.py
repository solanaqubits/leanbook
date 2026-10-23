"""Exercise the ordinary Python client in a child with an isolated loader path."""
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import tempfile

expected = Path(os.environ['EXPECTED_SQLITE']).resolve()
mapped = sorted({Path(line.split()[-1]).resolve() for line in Path('/proc/self/maps').read_text().splitlines()
                 if '/libsqlite3.so' in line})
assert mapped == [expected], mapped
with tempfile.TemporaryDirectory(prefix='sqlite-qualified-client-') as temp:
    path = Path(temp) / 'synthetic.sqlite'
    c = sqlite3.connect(path)
    assert c.execute('PRAGMA journal_mode=WAL').fetchone() == ('wal',)
    c.execute('PRAGMA synchronous=FULL')
    c.execute('PRAGMA busy_timeout=2000')
    c.execute('PRAGMA foreign_keys=ON')
    c.execute('CREATE TABLE t(id INTEGER PRIMARY KEY, value BLOB UNIQUE)')
    c.executemany('INSERT INTO t VALUES (?,?)', [(i, bytes([i]) * 512) for i in range(100)])
    c.commit()
    c.execute('UPDATE t SET value=? WHERE id=0', (b'rollback',))
    c.rollback()
    assert c.execute('SELECT value FROM t WHERE id=0').fetchone()[0] == bytes(512)
    checkpoints = {}
    for mode in ['PASSIVE', 'FULL', 'RESTART', 'TRUNCATE']:
        checkpoints[mode] = c.execute('PRAGMA wal_checkpoint(' + mode + ')').fetchone()
        assert checkpoints[mode][0] == 0
    options = sorted(row[0] for row in c.execute('PRAGMA compile_options'))
    source_id = c.execute('SELECT sqlite_source_id()').fetchone()[0]
    c.close()
    c = sqlite3.connect(path)
    assert c.execute('PRAGMA integrity_check').fetchone() == ('ok',)
    assert c.execute('SELECT count(*) FROM t').fetchone() == (100,)
    assert c.execute('SELECT id,value FROM t ORDER BY id').fetchall() == [(i, bytes([i])*512) for i in range(100)]
    c.close()
print(json.dumps({'ok': True, 'mapped': str(expected), 'sha256': hashlib.sha256(expected.read_bytes()).hexdigest(),
                  'version': sqlite3.sqlite_version, 'source_id': source_id, 'compile_options': options,
                  'checkpoints': checkpoints, 'rows_after_reopen': 100}, indent=2))
