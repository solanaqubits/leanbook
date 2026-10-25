"""Classify textual Lean invocation candidates; not a complete call-graph audit.

The historical scope/pattern reproduces Fable's 232-line inventory. Additional
tracked text files are reported separately, so documentation is not silently
counted as an executable bypass. Dynamic/multiline constructions need review.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess

PATTERN = re.compile(
    r"'env',\s*'lean'|\"env\",\s*\"lean\"|lake env lean|\['lean'|\[\"lean\"|\('lean'")


def category(name, line):
    if '--print-prefix' in line or '--version' in line:
        return 'runtime-query-no-elaboration'
    if (name.endswith(('.md', '.rst', '.txt')) or line.lstrip().startswith('#')
            or 'Usage: lake env lean' in line):
        return 'documentation-or-comment'
    if name.startswith('tests/'):
        return 'test-driver-candidate'
    if name.startswith('.github/workflows/') or name == 'tools/release_evidence.py':
        return 'release-or-ci-gate'
    return 'tool-or-generated-input-driver-candidate'


def inventory(root):
    root = Path(root)
    historical = set()
    for pattern in ('tools/**/*.py', 'tests/*.py', 'scripts/*.py',
                    '.github/workflows/*.yml'):
        historical.update(str(p.relative_to(root)) for p in root.glob(pattern))
    tracked = subprocess.check_output(
        ['git', 'ls-files', '-z'], cwd=root).decode().split('\0')
    rows = []
    for name in sorted(historical | {n for n in tracked if n}):
        try:
            lines = (root / name).read_text().splitlines()
        except (UnicodeError, OSError):
            continue
        for number, line in enumerate(lines, 1):
            if PATTERN.search(line):
                rows.append(dict(file=name, line=number, code=line.strip(),
                                 scope='historical' if name in historical else 'supplemental',
                                 category=category(name, line)))
    return dict(schema_version=1, rows=rows,
                counts={scope: dict(Counter(r['category'] for r in rows
                                           if r['scope'] == scope))
                        for scope in ('historical', 'supplemental')},
                limitation='Textual candidates, not proof of exhaustive runtime coverage')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('root', type=Path)
    print(json.dumps(inventory(p.parse_args().root), indent=2))
