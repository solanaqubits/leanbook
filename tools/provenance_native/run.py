#!/usr/bin/env python3
"""Launch a trusted Lean IO client with the qualified native adapter.
This runs local code; it is not an untrusted-script sandbox or general package CLI.
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path
from build import build, qualify, ROOT, HERE


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', type=Path, default=HERE/'profile.json')
    parser.add_argument('script', type=Path)
    parser.add_argument('args', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    try:
        profile=json.loads(args.profile.read_text())
        shim=build(ROOT/'.lake/provenance-native',profile)
        qualify(profile)
        command=['lake','env','lean','-j1','-DwarningAsError=true',
                 '--load-dynlib='+str(shim),'--run',str(args.script.resolve()),
                 profile['library_path'],profile['library_version'],*args.args]
        return subprocess.run(command,cwd=ROOT).returncode
    except (ValueError,OSError,subprocess.SubprocessError) as e:
        print('backend_failure: '+str(e),file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
