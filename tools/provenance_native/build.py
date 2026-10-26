#!/usr/bin/env python3
"""Build the IO shim; qualify a pinned local libsodium binary before launch.
This is a trusted-host identity check, not hostile-filesystem race protection.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.lean_invoke import lean_command
import argparse
import hashlib
import json
import re
import platform
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def qualify(profile):
    if profile.get('schema') != 'provenance-native-profile-v1' or profile.get('platform') != 'linux-x86_64':
        raise ValueError('backend_failure: unsupported qualification profile')
    if sys.platform != 'linux' or platform.machine() != 'x86_64':
        raise ValueError('backend_failure: unqualified platform')
    path = Path(profile['library_path'])
    if not path.is_absolute() or not path.is_file():
        raise ValueError('backend_failure: missing absolute library path')
    if hashlib.sha256(path.read_bytes()).hexdigest() != profile['library_sha256']:
        raise ValueError('backend_failure: unqualified library binary')
    return path


def build(output, profile):
    qualify(profile)
    output.mkdir(parents=True, exist_ok=True)
    prefix = subprocess.check_output(['lean', '--print-prefix'], text=True).strip()
    shim = output / 'libprovenance_native.so'
    libroot = ROOT/'.lake/build/lib/lean/tools/provenance_native'
    libroot.mkdir(parents=True, exist_ok=True)
    raw_c = output/'Raw.c'
    subprocess.run(lean_command(['-j1', '-DwarningAsError=true', '-o', str(libroot / 'Raw.olean'), '-c', str(raw_c), str(HERE / 'Raw.lean')], lake='lake'),
                   cwd=ROOT, check=True)
    prototypes = re.findall(r'^lean_object\* provenance_(?:verify|sha256)_io\([^\n]+;', raw_c.read_text(), re.M)
    if len(prototypes) != 2:
        raise ValueError('Unrecognized Lean IO ABI; requalify before compiling')
    abi = output/'ffi_abi.h'
    abi.write_text('#include <lean/lean.h>\n'+'\n'.join(prototypes)+'\n')
    cmd = ['cc', '-std=c11', '-Wall', '-Wextra', '-Werror', '-O2', '-fPIC', '-shared',
           '-I' + str(Path(prefix) / 'include'), '-include', str(abi), str(HERE / 'ffi.c'), str(raw_c),
           '-ldl', '-o', str(shim)]
    subprocess.run(cmd, check=True)
    subprocess.run(lean_command(['-j1', '-DwarningAsError=true', '-o', str(libroot / 'Adapter.olean'), str(HERE / 'Adapter.lean')], lake='lake'),
                   cwd=ROOT, check=True)
    receipt = dict(profile=profile, lean_version=subprocess.check_output(['lean','--version'],text=True).strip(),
                   raw_sha256=hashlib.sha256((HERE/'Raw.lean').read_bytes()).hexdigest(),
                   adapter_sha256=hashlib.sha256((HERE/'Adapter.lean').read_bytes()).hexdigest(), compiler=subprocess.check_output(['cc','--version'],text=True).splitlines()[0],
                   command=cmd, shim_sha256=hashlib.sha256(shim.read_bytes()).hexdigest(),
                   ffi_sha256=hashlib.sha256((HERE/'ffi.c').read_bytes()).hexdigest())
    (output / 'build-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    return shim


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile', type=Path, default=HERE/'profile.json')
    p.add_argument('--output', type=Path, default=ROOT/'.lake/provenance-native')
    args = p.parse_args()
    try:
        print(build(args.output.resolve(), json.loads(args.profile.read_text())))
    except (ValueError, OSError, subprocess.SubprocessError) as e:
        print(str(e), file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
