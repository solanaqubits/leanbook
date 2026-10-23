"""Explicit isolated SQLite runtime installation and anchored CLI launcher.

Trusted Linux host only. No system library replacement, DB initialization or
Witness reset. Existing checkpoint identity is independent of execution profile.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def profile():
    return json.loads((HERE / 'profile.json').read_text())


def verified_library():
    p = profile()
    lib = Path(p['library_path'])
    if (not lib.is_absolute() or lib.is_symlink() or not lib.is_file()
            or hashlib.sha256(lib.read_bytes()).hexdigest() != p['library_sha256']):
        raise ValueError('runtime_library_mismatch')
    info = lib.stat()
    if info.st_uid not in (0, os.geteuid()) or info.st_mode & 0o022:
        raise ValueError('unsafe_runtime_permissions')
    alias = lib.parent / 'libsqlite3.so.0'
    if not alias.is_symlink() or os.readlink(alias) != lib.name:
        raise ValueError('runtime_soname_mismatch')
    # A dedicated protected loader directory, never a generic search directory.
    for directory in [lib.parent, *lib.parent.parents]:
        st = directory.stat()
        if st.st_uid not in (0, os.geteuid()) or st.st_mode & 0o022:
            raise ValueError('unsafe_runtime_directory')
    if set(x.name for x in lib.parent.iterdir()) != {lib.name, alias.name}:
        raise ValueError('unexpected_runtime_contents')
    return lib


def install(source):
    """Copy only the already-qualified artifact to its pinned per-user location.

    Exclusive writes, no overwrites. A failed partial install needs operator review.
    No compiler/download/install-to-system command is executed.
    """
    p = profile()
    source = Path(source)
    if not source.is_file() or source.is_symlink():
        raise ValueError('invalid_runtime_source')
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != p['library_sha256']:
        raise ValueError('runtime_source_mismatch')
    target = Path(p['library_path'])
    if target.parent.exists():
        return verified_library()
    missing = []
    directory = target.parent
    while not directory.exists():
        missing.append(directory)
        directory = directory.parent
    for directory in reversed(missing):
        directory.mkdir(mode=0o700)
    with target.open('xb') as f:
        f.write(raw)
    target.chmod(0o500)
    (target.parent / 'libsqlite3.so.0').symlink_to(target.name)
    return verified_library()


def environment():
    lib = verified_library()
    if os.environ.get('LD_PRELOAD') or os.environ.get('LD_AUDIT'):
        raise ValueError('unsupported_loader_injection')
    env = dict(os.environ)
    env['LD_LIBRARY_PATH'] = str(lib.parent)
    return env


# A new interpreter selects the loader before SQLite import. Verify the mapped
# library (using an in-memory probe) before opening any registry file.
CHILD = '''
import json, runpy, sys
from tools.challenge_store.store import qualify_sqlite, StoreError
try:
    qualify_sqlite()
except (StoreError, OSError, ValueError):
    print(json.dumps(dict(status='error', error='runtime_qualification_failed',
        authorization='blocked', external_service_qualified=False)))
    sys.exit(2)
if sys.argv[1] == 'check':
    from tools.challenge_store.runtime import profile
    p = profile()
    print(json.dumps(dict(status='runtime_verified', library_path=p['library_path'],
        library_sha256=p['library_sha256'], authorization='blocked',
        external_service_qualified=False)))
else:
    sys.argv = ['anchored_cli'] + sys.argv[2:]
    runpy.run_module('tools.challenge_store.anchored_cli', run_name='__main__')
'''


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    setup = commands.add_parser('install')
    setup.add_argument('--source', required=True, type=Path)
    commands.add_parser('check')
    run = commands.add_parser('run')
    run.add_argument('arguments', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    try:
        if args.command == 'install':
            install(args.source)
            print(json.dumps(dict(status='runtime_installed', authorization='blocked')))
            return 0
        env = environment()
        arguments = getattr(args, 'arguments', [])
        if arguments[:1] == ['--']:
            arguments = arguments[1:]
        result = subprocess.run([sys.executable, '-c', CHILD, args.command, *arguments],
                                cwd=HERE.parents[1], env=env)
        return result.returncode
    except (OSError, ValueError):
        print(json.dumps(dict(status='error', error='runtime_setup_failed',
                             authorization='blocked', external_service_qualified=False)))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
