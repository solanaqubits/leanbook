"""Trusted-host CLI. Administrative operations are Python capability API only.
JSON request input is a local file. Output is not a physical authorization grant.
"""
import argparse
import json
from pathlib import Path
from .bridge import loads,MAX_WIRE
from .store import Store,StoreError

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--db',type=Path,required=True)
    p.add_argument('operation',choices=['register','commit','resolve','lookup','inspect','submit-files'])
    p.add_argument('--input',type=Path)
    p.add_argument('--context-version')
    for name in ('manifest','signature','snapshot','profile'):
        p.add_argument('--'+name,type=Path)
    a=p.parse_args()
    try:
        obj={}
        if a.operation not in ('inspect','submit-files'):
            if a.input is None:raise ValueError('--input required')
            with a.input.open('rb') as f:raw=f.read(MAX_WIRE+1)
            if len(raw)>MAX_WIRE:raise ValueError('transport_limit_exceeded')
            obj=loads(raw)
        if a.operation=='submit-files':
            if a.input is None:raise ValueError('--input must contain txId')
            with a.input.open('rb') as f:raw=f.read(MAX_WIRE+1)
            if len(raw)>MAX_WIRE:raise ValueError('transport_limit_exceeded')
            obj=loads(raw)
            if not a.context_version or any(getattr(a,n) is None for n in ('manifest','signature','snapshot','profile')):
                raise ValueError('submit-files requires context version and all four file paths')
        with Store(a.db) as s:
            if a.operation=='register':out=s.register(obj['txId'],obj['request'])
            elif a.operation=='commit':out=s.commit_checked(obj['txId'],obj['request'])
            elif a.operation=='resolve':out=s.resolve(obj['key'],obj['txId'])
            elif a.operation=='lookup':out=s.lookup(obj['key'])
            elif a.operation=='submit-files':
                from .files import FilePackage,submit_files
                out=submit_files(s,obj['txId'],a.context_version,FilePackage(a.manifest,a.signature,a.snapshot,a.profile))
            else:out=s.inspect()
        print(json.dumps({'ok':out},ensure_ascii=False))
        return 0
    except (StoreError,ValueError,KeyError,OSError) as e:
        print(json.dumps({'error':getattr(e,'code','invalid_input'),'detail':str(e)}))
        return 2
if __name__=='__main__':raise SystemExit(main())
