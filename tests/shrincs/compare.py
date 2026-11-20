"""Usage from project root: python3 tests/shrincs/compare.py /path/to/pinned/impl/shrincs.py"""
import hashlib
import json
import runpy
import subprocess
import sys
from pathlib import Path

reference = Path(sys.argv[1])
digest = hashlib.sha256(reference.read_bytes()).hexdigest()
if digest != "4ac47c4b463f09e82376f24d3d16a1283695f61d7c10175a6a036cbf94691094":
    raise ValueError("Unexpected reference bytes")
select = runpy.run_path(str(reference))["shrincs_sf_leaf_select"]
maximum = 2**64 - 1
inputs, expected = [], []
for depth in range(256):
    for shape in (0, 1, 2, 255):
        limit = 2**depth if shape == 1 else depth + 1
        edge = {0, 1, 2, depth, maximum, maximum-1, limit-2, limit-1, limit, limit+1}
        if shape == 0 or (shape == 1 and depth <= 10):
            edge.update(range(limit))
        for counter in [None, *sorted(x for x in edge if 0 <= x <= maximum)]:
            inputs.append(f"{shape} {depth} {'-' if counter is None else counter}")
            answer = select(bytes([shape, depth]), counter)
            expected.append("-" if answer is None else f"{answer[0]} {answer[1]}")
output = subprocess.run(["lake", "env", "lean", "--run", "tests/shrincs/LeafCLI.lean"],
                        input="\n".join(inputs)+"\n", capture_output=True, text=True, check=True)
actual = output.stdout.splitlines()
if len(actual) != len(expected):
    raise AssertionError((len(expected), len(actual)))
for case, a, e in zip(inputs, actual, expected):
    if a != e:
        raise AssertionError((case, a, e))
print(json.dumps(dict(cases=len(inputs), mismatches=0, reference_sha256=digest)))
