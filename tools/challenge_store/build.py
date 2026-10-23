#!/usr/bin/env python3
"""Build only the runtime transport. Existing formal sources remain unchanged."""
import hashlib
import json
import sqlite3
import subprocess
from pathlib import Path
from tools.provenance_native.build import build as native_build
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent

def build():
    p = json.loads((ROOT/'tools/provenance_native/profile.json').read_text())
    native_build(ROOT/'.lake/provenance-native', p)
    dest = ROOT/'.lake/build/lib/lean/tools/challenge_store'
    dest.mkdir(parents=True, exist_ok=True)
    for name in ['Wire', 'FileManifest', 'Worker']:
        subprocess.run(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true',
                        '-o', str(dest/(name+'.olean')), str(HERE/(name+'.lean'))],
                       cwd=ROOT, check=True)
    receipt = {'sqlite_version': sqlite3.sqlite_version, 'sqlite_source_id':
        sqlite3.connect(':memory:').execute('select sqlite_source_id()').fetchone()[0],
        'schema_sha256': hashlib.sha256((HERE/'schema.sql').read_bytes()).hexdigest()}
    (ROOT/'.lake/provenance-native/sqlite-build.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt
if __name__ == '__main__':
    print(json.dumps(build(),indent=2))
