"""Run the clean-project check in a local pinned Linux Docker image.

No image pull; dependency/toolchain mounts are read-only. This is a build
launcher, not the separate SimLab benchmark watchdog or a full beta driver.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time
import uuid


def launch(root, output, image):
    root, output = Path(root).resolve(), Path(output).resolve()
    if output.is_relative_to(root):
        raise ValueError('evidence must be outside project')
    if not image.startswith('sha256:') or len(image) != 71:
        raise ValueError('pin an already installed image by full sha256 ID')
    subprocess.run(['docker', 'image', 'inspect', image], check=True, stdout=subprocess.DEVNULL)
    output.mkdir(parents=True, exist_ok=False)
    prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                        cwd=root, text=True).strip()).resolve()
    common = Path(subprocess.check_output(['git', 'rev-parse', '--git-common-dir'],
                                        cwd=root, text=True).strip())
    if not common.is_absolute(): common = (root / common).resolve()
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages = {(root / '.lake/packages').resolve()}
    packages.update((root / '.lake/packages' / p['name']).resolve() for p in manifest['packages'])
    name = 'lean-clean-' + uuid.uuid4().hex[:16]
    cmd = ['docker', 'run', '--detach', '--pull=never', '--name', name,
           '--network=none', '--read-only', '--memory=12g', '--memory-swap=12g',
           '--cpus=4', '--pids-limit=512', '--cgroupns=private', '--cap-drop=ALL',
           '--security-opt=no-new-privileges', '--user', f'{os.getuid()}:{os.getgid()}',
           '--tmpfs', '/tmp:rw,nosuid,nodev,size=512m', '--workdir', str(root),
           '--entrypoint', '/usr/bin/python3', '--env', 'HOME=/tmp',
           '--env', 'PYTHONDONTWRITEBYTECODE=1', '--env', 'LEAN_NUM_THREADS=4',
           '--env', 'LEAN_CLEAN_REQUIRE_LIMITS=1',
           '--env', f'PATH={prefix}/bin:/usr/bin:/bin']
    for path in sorted({Path('/usr'), Path('/bin'), Path('/lib'), Path('/lib64'),
                        prefix, common, *packages}):
        cmd += ['--volume', f'{path}:{path}:ro']
    for path in (root, output):
        cmd += ['--volume', f'{path}:{path}:rw']
    cmd += [image, 'tools/clean_project_build.py', '--output', str(output / 'clean-project')]
    (output / 'container-command.json').write_text(json.dumps(cmd, indent=2) + '\n')
    status = dict(container=name, status='starting', timeout=False, wall_limit_seconds=3700)
    start = time.monotonic()
    attempted = False
    try:
        attempted = True
        subprocess.run(cmd, check=True, capture_output=True, text=True, timeout=60)
        try:
            waited = subprocess.run(['docker', 'wait', name], check=True,
                                    capture_output=True, text=True, timeout=3700)
            status['exit_code'] = int(waited.stdout.strip())
            status['status'] = 'passed' if status['exit_code'] == 0 else 'failed'
        except subprocess.TimeoutExpired:
            status.update(status='timeout', timeout=True)
            subprocess.run(['docker', 'kill', name], check=True, capture_output=True, timeout=30)
    finally:
        if attempted:
            for args, filename in [(['inspect', name], 'container-inspect.json'),
                                   (['logs', name], 'container.log')]:
                with (output / filename).open('w') as log:
                    subprocess.run(['docker', *args], stdout=log, stderr=subprocess.STDOUT,
                                   check=False, timeout=30)
            subprocess.run(['docker', 'rm', '-f', name], check=False,
                           capture_output=True, timeout=30)
        status['elapsed_seconds'] = time.monotonic() - start
        (output / 'status.json').write_text(json.dumps(status, indent=2) + '\n')
    if status['status'] != 'passed':
        raise RuntimeError('container clean build did not pass: ' + str(status))
    return status


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--image', required=True)
    a = p.parse_args()
    print(json.dumps(launch(a.project, a.output, a.image)))
