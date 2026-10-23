"""Identical external VFS controls on new synthetic DBs; no live DB path input.

Usage: python3 run_controls.py HARNESS OLD_LIBRARY NEW_LIBRARY NEW_RESULT_DIRECTORY
Exit 0 requires all expected positive and negative controls. Harness exit 2 is
always failure, never evidence of the WAL-reset bug.
"""
import json
from pathlib import Path
import subprocess
import sys

harness, old, new, output = map(lambda x: Path(x).resolve(), sys.argv[1:])
output.mkdir(exist_ok=False)
results = []
for name, lib in [('baseline',old),('patched',new)]:
    for mode in ['plain','inject']:
        for repeat in range(3):
            case = f'{name}-{mode}-{repeat}'
            proc = subprocess.run([str(harness),str(lib),str(output/(case+'.sqlite')),mode],
                                  capture_output=True, text=True, timeout=30)
            (output/(case+'.log')).write_text(proc.stdout+proc.stderr)
            expected = 1 if name == 'baseline' and mode == 'inject' else 0
            fired = 'fired=1' in proc.stdout if mode == 'inject' else 'fired=0' in proc.stdout
            results.append(dict(case=case, returncode=proc.returncode, expected=expected,
                                matched=proc.returncode==expected and fired))
(output/'results.json').write_text(json.dumps(results,indent=2)+'\n')
raise SystemExit(0 if all(r['matched'] for r in results) else 1)
