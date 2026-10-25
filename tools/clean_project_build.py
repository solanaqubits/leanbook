"""Clean project-only Lake build with source, coverage and artifact receipts.

Trusted, isolated checkouts only. External package build directories must be
mounted read-only. Receipts are execution records, not signed attestations.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time
import tomllib

SCHEMA = 'LEAN-CLEAN-PROJECT-BUILD-1'
ENV = {'LAKE_ARTIFACT_CACHE': 'false', 'LAKE_CACHE_DIR': '', 'LAKE_NO_CACHE': 'true'}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024**2), b''):
            h.update(chunk)
    return h.hexdigest()


def files(directory):
    return {str(p.relative_to(directory)): sha(p) for p in sorted(directory.rglob('*'))
            if p.is_file()}


def resources():
    result = {}
    for name in ('memory.max', 'memory.swap.max', 'memory.peak', 'memory.events', 'cpu.max'):
        p = Path('/sys/fs/cgroup') / name
        if p.exists(): result[name] = p.read_text().strip()
    return result


def source_inputs(root):
    names = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'], cwd=root)
    return {n: sha(root / n) for n in sorted(set(names.decode().split('\0')))
            if n and (root / n).is_file()}


def project_plan(root):
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    # Refuse layouts whose targets/artifact paths this implementation cannot prove.
    for key in ('buildDir', 'srcDir', 'leanLibDir', 'nativeLibDir', 'irDir', 'binDir'):
        if key in config:
            raise ValueError('unsupported custom path: ' + key)
    modules = set()
    for lib in config.get('lean_lib', []):
        if set(lib) != {'name'}:
            raise ValueError('unsupported library configuration')
        name = lib['name']
        stem = root / name.replace('.', '/')
        if stem.with_suffix('.lean').is_file():
            modules.add(name)
        modules.update(str(p.relative_to(root))[:-5].replace('/', '.')
                       for p in stem.rglob('*.lean'))
    executables = {}
    for exe in config.get('lean_exe', []):
        if set(exe) != {'name', 'root'}:
            raise ValueError('unsupported executable configuration')
        executables[exe['name']] = exe['root']
        modules.add(exe['root'])
    if not modules:
        raise ValueError('empty project graph')
    for name in modules:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', name):
            raise ValueError('unsupported module name')
        if not (root / (name.replace('.', '/') + '.lean')).is_file():
            raise ValueError('missing source: ' + name)
    for name in executables:
        if not re.fullmatch(r'[A-Za-z0-9_-]+', name):
            raise ValueError('unsupported executable name')
    return dict(modules=sorted(modules), executables=executables)


def dependency_state(root, require_readonly=True):
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    if manifest.get('packagesDir', '.lake/packages') != '.lake/packages':
        raise ValueError('unsupported packages directory')
    result = {}
    for pkg in manifest['packages']:
        name = pkg['name']
        if not re.fullmatch(r'[A-Za-z0-9_-]+', name):
            raise ValueError('invalid dependency name')
        path = (root / '.lake/packages' / name).resolve()
        if path.is_relative_to(root / '.lake/build'):
            raise ValueError('dependency overlaps project build')
        if not path.is_dir():
            raise ValueError('missing dependency: ' + name)
        readonly = bool(os.statvfs(path).f_flag & os.ST_RDONLY)
        if require_readonly and not readonly:
            raise ValueError('dependency must be mounted read-only: ' + name)
        result[name] = dict(path=str(path), artifacts=files(path / '.lake/build'))
    return result


def clean_project(root):
    lake, build = root / '.lake', root / '.lake/build'
    if lake.is_symlink() or build.is_symlink():
        raise ValueError('refusing symlinked project build path')
    if build.exists():
        shutil.rmtree(build)  # only this checkout; never .lake/packages
    build.mkdir(parents=True)
    if list(build.iterdir()):
        raise ValueError('project build not empty')


def build_command(plan):
    return ['lake', '--no-cache', '--no-ansi', '--verbose', 'build', '--wfail',
            *('+' + m for m in plan['modules']), *plan['executables']]


def log_targets(text, status):
    return sorted(set(re.findall(r'^.*?\[\d+/\d+\] ' + status + r' (\S+)', text, re.M)))


def check_coverage(root, plan, text, started_ns):
    built = log_targets(text, 'Built')
    replayed = log_targets(text, 'Replayed')
    expected = set(plan['modules'])
    if expected - set(built) or expected & set(replayed):
        raise ValueError('incomplete fresh module coverage: ' + str(sorted(expected - set(built))))
    artifacts = files(root / '.lake/build')
    actual_modules = {p[len('lib/lean/'):-len('.olean')].replace('/', '.')
                      for p in artifacts if p.startswith('lib/lean/') and p.endswith('.olean')}
    if actual_modules != expected:
        raise ValueError('project olean set differs from planned module set')
    traces = {}
    for module in plan['modules']:
        stem = module.replace('.', '/')
        required = ['lib/lean/' + stem + suffix for suffix in ('.olean', '.ilean', '.trace')]
        required.append('ir/' + stem + '.c')
        for name in required:
            path = root / '.lake/build' / name
            if name not in artifacts or path.is_symlink() or path.stat().st_mtime_ns < started_ns:
                raise ValueError('missing/nonfresh artifact: ' + name)
        trace = json.loads((root / '.lake/build/lib/lean' / (stem + '.trace')).read_text())
        if trace.get('synthetic') is not False or 'depHash' not in trace:
            raise ValueError('invalid module trace: ' + module)
        traces[module] = trace['depHash']
    for name in plan['executables']:
        binary = root / '.lake/build/bin' / name
        if ('bin/' + name not in artifacts or binary.is_symlink()
                or binary.stat().st_mtime_ns < started_ns):
            raise ValueError('missing/nonfresh executable: ' + name)
    return dict(fresh_modules=sorted(expected), fresh_module_count=len(expected),
                built_targets=built, replayed_targets=replayed,
                artifacts=artifacts, trace_dep_hashes=traces)


def reused_packages(dependencies, coverage):
    replayed = set(coverage['replayed_targets'])
    result = []
    for name, dep in dependencies.items():
        modules = {p[len('lib/lean/'):-len('.olean')].replace('/', '.')
                   for p in dep['artifacts'] if p.startswith('lib/lean/') and p.endswith('.olean')}
        if replayed & modules:
            result.append(name)
    return sorted(result)


def validate_receipt(root, directory):
    root, directory = Path(root).resolve(), Path(directory).resolve()
    r = json.loads((directory / 'receipt.json').read_text())
    if (r.get('schema') != SCHEMA or r.get('status') != 'passed'
            or r.get('empty_start') is not True or r.get('cache_environment') != ENV
            or r.get('dependencies_readonly') is not True):
        raise ValueError('invalid clean-build receipt')
    if r['plan'] != project_plan(root) or r['inputs'] != source_inputs(root):
        raise ValueError('clean-build source/target binding mismatch')
    if r['command'] != build_command(r['plan']) or sha(directory / 'build.log') != r['log_sha256']:
        raise ValueError('clean-build command/log mismatch')
    deps = dependency_state(root, require_readonly=False)
    if deps != r['dependencies_before'] or deps != r['dependencies_after']:
        raise ValueError('dependency artifacts changed')
    coverage = check_coverage(root, r['plan'], (directory / 'build.log').read_text(), r['started_ns'])
    # Subsequent beta checks may add separate artifacts; frozen ones must remain exact.
    for name, h in r['coverage']['artifacts'].items():
        if coverage['artifacts'].get(name) != h:
            raise ValueError('project artifact changed: ' + name)
    for key in ('fresh_modules', 'fresh_module_count', 'built_targets', 'replayed_targets', 'trace_dep_hashes'):
        if r['coverage'][key] != coverage[key]:
            raise ValueError('coverage receipt mismatch')
    if r['exit_code'] != 0:
        raise ValueError('failed clean build')
    reused = reused_packages(deps, coverage)
    if r['reused_dependency_packages'] != reused or r['reused_dependency_package_count'] != len(reused):
        raise ValueError('dependency reuse count mismatch')
    return r


def run(root, directory, timeout=3600):
    root, directory = Path(root).resolve(), Path(directory).resolve()
    if directory.is_relative_to(root):
        raise ValueError('evidence must be outside project')
    directory.mkdir(parents=True, exist_ok=False)
    if (root / '.lake').is_symlink() or (root / '.lake/build').is_symlink():
        raise ValueError('refusing symlinked project build path')
    (root / '.lake').mkdir(exist_ok=True)
    receipt = dict(schema=SCHEMA, status='running', cache_environment=ENV)
    with (root / '.lake/clean-build.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            receipt['resources_before'] = resources()
            if os.environ.get('LEAN_CLEAN_REQUIRE_LIMITS') == '1':
                observed = receipt['resources_before']
                if (observed.get('memory.max') != str(12 * 1024**3)
                        or observed.get('memory.swap.max') != '0'
                        or observed.get('cpu.max') != '400000 100000'):
                    raise ValueError('container resource contract mismatch')
            receipt.update(plan=project_plan(root), inputs=source_inputs(root))
            for module in receipt['plan']['modules']:
                if module.replace('.', '/') + '.lean' not in receipt['inputs']:
                    raise ValueError('planned source absent from input manifest: ' + module)
            print('Hashing read-only dependency artifacts', flush=True)
            receipt['dependencies_before'] = dependency_state(root)
            receipt['dependencies_readonly'] = True
            clean_project(root)
            receipt.update(empty_start=True, started_ns=time.time_ns())
            receipt['command'] = build_command(receipt['plan'])
            print('Building ' + str(len(receipt['plan']['modules'])) + ' project modules', flush=True)
            with (directory / 'build.log').open('w') as log:
                p = subprocess.Popen(receipt['command'], cwd=root,
                                     env={**os.environ, **ENV}, stdout=log,
                                     stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    receipt['exit_code'] = p.wait(timeout=timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(p.pid, signal.SIGKILL); p.wait()
                    receipt['timeout'] = True
                    raise ValueError('clean build timeout')
            receipt['log_sha256'] = sha(directory / 'build.log')
            receipt['dependencies_after'] = dependency_state(root)
            if receipt['dependencies_after'] != receipt['dependencies_before']:
                raise ValueError('dependency artifacts changed during build')
            if source_inputs(root) != receipt['inputs']:
                raise ValueError('source changed during build')
            if receipt['exit_code']:
                raise ValueError('strict build failed')
            receipt['coverage'] = check_coverage(root, receipt['plan'],
                                                (directory / 'build.log').read_text(),
                                                receipt['started_ns'])
            reused = reused_packages(receipt['dependencies_before'], receipt['coverage'])
            receipt.update(status='passed', reused_dependency_packages=sorted(reused),
                           reused_dependency_package_count=len(reused))
        except Exception as exc:
            receipt.update(status='failed', error=str(exc))
            raise
        finally:
            receipt['resources_after'] = resources()
            receipt['finished_ns'] = time.time_ns()
            (directory / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return receipt


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    run(a.project, a.output)
