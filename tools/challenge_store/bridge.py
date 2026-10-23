"""Private bounded JSON transport to the explicit Lean/native IO worker."""
import json
import os
import select
import subprocess
import time
from pathlib import Path
from tools.provenance_native.build import qualify
ROOT = Path(__file__).resolve().parents[2]
MAX_WIRE = 8 * 1024 * 1024

def loads(raw):
    def pairs(items):
        obj = {}
        for k,v in items:
            if k in obj: raise ValueError('duplicate JSON key')
            obj[k] = v
        return obj
    return json.loads(raw, object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))

def dumps(obj):
    return json.dumps(obj, ensure_ascii=True, separators=(',', ':'), sort_keys=True, allow_nan=False)

class Bridge:
    def __init__(self, timeout=30):
        p=loads((ROOT/'tools/provenance_native/profile.json').read_text())
        qualify(p)
        shim=ROOT/'.lake/provenance-native/libprovenance_native.so'
        if not shim.is_file(): raise RuntimeError('run python3 -m tools.challenge_store.build first')
        self.timeout=timeout
        self.process=subprocess.Popen(['lake','env','lean','-j1','-DwarningAsError=true',
            '--load-dynlib='+str(shim),'--run',str(ROOT/'tools/challenge_store/Worker.lean'),
            p['library_path'],p['library_version']],cwd=ROOT,stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,bufsize=0)
        os.set_blocking(self.process.stdin.fileno(),False)
        os.set_blocking(self.process.stdout.fileno(),False)
    def call(self, obj):
        raw=(dumps(obj)+'\n').encode()
        if len(raw)>MAX_WIRE: raise ValueError('transport_limit_exceeded')
        deadline=time.monotonic()+self.timeout
        try:
            view=memoryview(raw)
            while view:
                left=deadline-time.monotonic()
                if left<=0 or not select.select([], [self.process.stdin], [], left)[1]:
                    raise TimeoutError('model worker timeout')
                view=view[os.write(self.process.stdin.fileno(),view):]
            answer=bytearray()
            while not answer.endswith(b'\n'):
                left=deadline-time.monotonic()
                if left<=0 or not select.select([self.process.stdout],[],[],left)[0]:
                    raise TimeoutError('model worker timeout')
                part=os.read(self.process.stdout.fileno(),65536)
                if not part: raise RuntimeError('model worker exited')
                answer.extend(part)
                if len(answer)>MAX_WIRE: raise ValueError('transport_limit_exceeded')
            result=loads(answer)
            if 'error' in result: raise ValueError(result['error'])
            return result['ok']
        except BaseException:
            self.close()
            raise
    def close(self):
        if self.process.poll() is None:
            self.process.kill()
        self.process.wait()
        self.process.stdin.close(); self.process.stdout.close()
