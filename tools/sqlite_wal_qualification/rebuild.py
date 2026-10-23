"""Reproduce the isolated build procedure; not a byte-reproducibility claim.

Usage: python3 rebuild.py AUTHENTICATED_VENDOR_SOURCE NEW_OUTPUT_DIRECTORY
Never installs a library or modifies the supplied source tree.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

here = Path(__file__).resolve().parent
source, output = map(lambda x: Path(x).resolve(), sys.argv[1:])
output.mkdir(exist_ok=False)
config = json.loads((here/'build-environment-final.json').read_text())
manifest = json.loads((here/'source-manifest.json').read_text())
env = dict(os.environ, **config['flags'], LC_ALL='C')
for name in ['baseline', 'patched']:
    src = output/name
    shutil.copytree(source, src, ignore=shutil.ignore_patterns('.pc','www'))
    actual = {str(p.relative_to(src)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in src.rglob('*') if p.is_file()}
    if actual != manifest:
        raise SystemExit('Vendor source differs from qualified source manifest')
    if name == 'patched':
        subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(here/'wal-reset-backport.patch')], cwd=src, check=True)
    build = output/(name+'-build')
    build.mkdir()
    for label, command in [('configure',[str(src/'configure'),*config['configure']]),
                           ('headers',['make','sqlite3.h']), ('make',['make','-j2','libsqlite3.la'])]:
        with (output/(name+'-'+label+'.log')).open('x') as log:
            subprocess.run(command, cwd=build, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    lib = build/'.libs/libsqlite3.so.0.8.6'
    print(name, hashlib.sha256(lib.read_bytes()).hexdigest(), lib, flush=True)
