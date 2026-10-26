"""Configured elaboration in a trusted Lake project (not a sandbox)."""
import argparse
from pathlib import Path
import subprocess


def elaborate_command(path, *, lake='lake', extra_args=()):
    """Keep compiler options after Lake's separator; inherit project options."""
    return [str(lake), 'lean', str(path), '--', '-j1',
            '-DwarningAsError=true', *extra_args]


def lean_command(args, *, lake='lake'):
    """Translate reviewed compiler/runtime arguments into configured Lake execution.

    Fail closed on unknown options. --run consumes a repeated source filename:
    Lake appends our arguments *after* its own filename and module setup flags.
    Runtime arguments after that filename are opaque, including leading dashes.
    """
    args = [str(x) for x in args]
    options = []
    i = 0
    while i < len(args):
        arg = args[i]
        if arg == '--run':
            if i+1 >= len(args) or not args[i+1].endswith('.lean'):
                raise ValueError('--run requires a Lean source file')
            return elaborate_command(args[i+1], lake=lake,
                                     extra_args=[*options, *args[i:]])
        if arg in ('-o', '-c'):
            if i+1 >= len(args):
                raise ValueError('Missing compiler output path')
            options.extend(args[i:i+2]); i += 2; continue
        if arg.startswith('-D'):
            if arg not in ('-DwarningAsError=true', '-DrelaxedAutoImplicit=false'):
                raise ValueError('Invalid option or warning policy override')
            options.append(arg)
        elif arg == '--json' or arg.startswith('--load-dynlib=') or (arg.startswith('-j') and arg[2:].isdigit()):
            options.append(arg)
        elif arg.endswith('.lean') and not arg.startswith('-'):
            if i != len(args)-1:
                raise ValueError('Runtime arguments require explicit --run')
            return elaborate_command(arg, lake=lake, extra_args=options)
        else:
            raise ValueError('Unreviewed Lean argument: '+arg)
        i += 1
    raise ValueError('Missing Lean source file')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('file')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    return subprocess.run(elaborate_command(args.file), cwd=root).returncode


if __name__ == '__main__':
    raise SystemExit(main())
