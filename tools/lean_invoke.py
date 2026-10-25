"""Configured elaboration in a trusted Lake project (not a sandbox)."""
import argparse
from pathlib import Path
import subprocess


def elaborate_command(path, *, lake='lake', extra_args=()):
    """Keep compiler options after Lake's separator; inherit project options."""
    return [str(lake), 'lean', str(path), '--', '-j1',
            '-DwarningAsError=true', *extra_args]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('file')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    return subprocess.run(elaborate_command(args.file), cwd=root).returncode


if __name__ == '__main__':
    raise SystemExit(main())
