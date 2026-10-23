"""SQLite local multi-process adapter for epsilon262.

Only trusted host code may open the DB or construct a Controller capability. Requests
never contain a verification report. Decisions come from the Lean/native IO worker.
No network server, credential system, anti-rollback or real-time guarantee is provided.
"""
import contextlib
import hashlib
import _sqlite3
import sqlite3
from pathlib import Path
from .bridge import Bridge, dumps, loads, MAX_WIRE
HERE=Path(__file__).resolve().parent
MAX_ROWS=2048

class StoreError(Exception):
    def __init__(self, code, detail=''):
        self.code=code
        super().__init__(code + (': '+detail if detail else ''))

class Controller:
    """In-process host capability. Do not deserialize or expose to request clients."""
    pass

def scope(k):
    s=k['scope']
    return (s['contextId'],s['sessionId'],s['policyVersion'])
def keytuple(k): return (*scope(k),bytes(k['challenge']))
def keydict(row):
    return {'scope':dict(zip(('contextId','sessionId','policyVersion'),row[:3])),
            'challenge':list(row[3])}
def tag(value): return value if isinstance(value,str) else next(iter(value))
def fail(code): raise StoreError(code)

def sqlite_error(e, writing=False):
    code=getattr(e,'sqlite_errorcode',0) & 255
    if code in (sqlite3.SQLITE_BUSY,sqlite3.SQLITE_LOCKED): return StoreError('lock_timeout')
    if code in (sqlite3.SQLITE_CORRUPT,sqlite3.SQLITE_NOTADB,sqlite3.SQLITE_CONSTRAINT):
        return StoreError('invalid_storage_state',str(e))
    return StoreError('write_failure' if writing else 'read_failure',str(e))

def schema_signature(db):
    return db.execute("SELECT type,name,tbl_name,sql FROM sqlite_schema WHERE name NOT LIKE 'sqlite_%' ORDER BY type,name").fetchall()

def expected_schema():
    with sqlite3.connect(':memory:') as db:
        db.executescript((HERE/'schema.sql').read_text())
        return schema_signature(db)

def qualify_sqlite():
    p=loads((HERE/'profile.json').read_text())
    with sqlite3.connect(':memory:') as db:
        source=db.execute('SELECT sqlite_source_id()').fetchone()[0]
    if sqlite3.sqlite_version!=p['sqlite_version'] or source!=p['sqlite_source_id']:
        fail('unqualified_configuration')
    for path,digest in [(Path(p['library_path']),p['library_sha256']),
                        (Path(_sqlite3.__file__),p['python_extension_sha256'])]:
        if hashlib.sha256(path.read_bytes()).hexdigest()!=digest:fail('unqualified_configuration')
    # Linux profile: identify the actual mapped SQLite library, not an unrelated file.
    mapped={line.split()[-1] for line in Path('/proc/self/maps').read_text().splitlines()
            if '/libsqlite3.so' in line}
    if mapped!={p['library_path']}:fail('unqualified_configuration')

class Store:
    def __init__(self,path,*,controller=None,timeout=2.0):
        qualify_sqlite()
        self.path=Path(path).resolve()
        if not self.path.is_file(): fail('store_not_initialized')
        self.controller=controller
        self.bridge=Bridge()
        self.db=None
        try:
            self.db=sqlite3.connect(self.path.as_uri()+'?mode=rw',uri=True,timeout=timeout,isolation_level=None)
            self.db.setlimit(sqlite3.SQLITE_LIMIT_LENGTH,MAX_WIRE)
            self.db.execute('PRAGMA foreign_keys=ON')
            self.db.execute('PRAGMA synchronous=FULL')
            self.db.execute('PRAGMA recursive_triggers=ON')
            if self.db.execute('PRAGMA journal_mode').fetchone()[0]!='wal': fail('unqualified_configuration')
            if self.db.execute('PRAGMA foreign_keys').fetchone()[0]!=1: fail('unqualified_configuration')
            if self.db.execute('PRAGMA synchronous').fetchone()[0]!=2: fail('unqualified_configuration')
            if self.db.execute('PRAGMA user_version').fetchone()[0]!=1: fail('invalid_storage_state')
            if schema_signature(self.db)!=expected_schema(): fail('invalid_storage_state')
            if self.db.execute('PRAGMA quick_check').fetchall()!=[('ok',)]: fail('invalid_storage_state')
            if self.db.execute('PRAGMA foreign_key_check').fetchall(): fail('invalid_storage_state')
        except BaseException:
            self.close()
            import sys
            e=sys.exception()
            if isinstance(e,sqlite3.Error):raise sqlite_error(e) from e
            raise
    @staticmethod
    def initialize(path,controller):
        if not isinstance(controller,Controller): fail('access_denied')
        qualify_sqlite()
        path=Path(path)
        # Exclusive creation: never initialize over an existing database.
        with path.open('xb'): pass
        path.chmod(0o600)
        db=sqlite3.connect(path,isolation_level=None)
        try:
            db.execute('PRAGMA journal_mode=WAL')
            db.execute('PRAGMA synchronous=FULL')
            db.execute('PRAGMA foreign_keys=ON')
            db.executescript('BEGIN IMMEDIATE;\n'+(HERE/'schema.sql').read_text()+'\nCOMMIT;')
        finally: db.close()
    def close(self):
        if self.db is not None: self.db.close()
        self.bridge.close()
    def __enter__(self): return self
    def __exit__(self,*_): self.close()
    def _admin(self,cap):
        if not isinstance(cap,Controller) or cap is not self.controller: fail('access_denied')
    @contextlib.contextmanager
    def _transaction(self,write):
        try: self.db.execute('BEGIN IMMEDIATE' if write else 'BEGIN')
        except sqlite3.Error as e: raise sqlite_error(e,write) from e
        try:
            if schema_signature(self.db)!=expected_schema(): fail('invalid_storage_state')
            yield
        except BaseException as e:
            try: self.db.rollback()
            except sqlite3.Error: pass
            if isinstance(e,sqlite3.Error): raise sqlite_error(e,write) from e
            raise
        else:
            try: self.db.commit()
            except sqlite3.Error as e:
                # Never infer ABORTED from a failed commit. Caller must resolve.
                try: self.db.rollback()
                except sqlite3.Error: pass
                raise StoreError('indeterminate_transaction_state',str(e)) from e
    def _rows(self,table):
        rows=self.db.execute('SELECT * FROM '+table+' LIMIT ?', (MAX_ROWS+1,)).fetchall()
        if len(rows)>MAX_ROWS: fail('storage_limit_exceeded')
        return rows
    def _image(self):
        image=dict(entries=[],transactions=[],contexts=[],active=[],accepted=[])
        # Bound materialized text/blobs before fetching them into Python.
        total=0
        for table in ('context_versions','active_contexts','challenge_entries','transactions'):
            if self.db.execute('SELECT count(*) FROM '+table).fetchone()[0]>MAX_ROWS:
                fail('storage_limit_exceeded')
            columns=[r[1] for r in self.db.execute('PRAGMA table_info('+table+')')]
            expr='+'.join('coalesce(length(CAST('+c+' AS BLOB)),0)' for c in columns)
            total+=self.db.execute('SELECT coalesce(sum('+expr+'),0) FROM '+table).fetchone()[0]
        if total>MAX_WIRE//4:fail('storage_limit_exceeded')
        entries={}
        for r in self._rows('context_versions'):
            cfg=loads(r[4]); e=cfg['expected']
            if tuple(e[x] for x in ('contextId','expectedSessionId','expectedPolicyVersion'))!=r[1:4]: fail('invalid_storage_state')
            image['contexts'].append([r[0],cfg])
        for r in self._rows('active_contexts'):
            image['active'].append([dict(zip(('contextId','sessionId','policyVersion'),r[:3])),r[3]])
        for r in self._rows('challenge_entries'):
            key=keydict(r)
            if r[4]=='ISSUED': entry='issued'
            else:
                rec=dict(payloadDigest=list(r[5]),pinnedContextVersion=r[6],historicalReport=loads(r[7]))
                entry={'consumed':{'record':rec}}
            entries[keytuple(key)]=entry
            image['entries'].append([key,entry])
        accepted=[]
        for r in self._rows('transactions'):
            key=keydict(r[1:5]); b=dict(key=key,message=list(r[5]))
            if r[6]=='PENDING': tx={'pending':{'binding':b}}
            elif r[6]=='ABORTED': tx={'aborted':{'binding':b,'reason':r[8]}}
            else:
                entry=entries.get(keytuple(key))
                if entry is None or tag(entry)!='consumed': fail('invalid_storage_state')
                rec=entry['consumed']['record']
                tx={'committed':dict(binding=b,record=rec,kind=r[7])}
                if r[7]=='newAcceptance': accepted.append((r[9],key))
            image['transactions'].append([r[0],tx])
        if sorted(a for a,_ in accepted)!=list(range(1,len(accepted)+1)): fail('invalid_storage_state')
        image['accepted']=[k for _,k in sorted(accepted,reverse=True)]
        consumed=[keytuple(k) for k,e in image['entries'] if tag(e)=='consumed']
        if set(consumed)!=set(keytuple(k) for _,k in accepted): fail('invalid_storage_state')
        if len(dumps(image).encode())>MAX_WIRE//2: fail('storage_limit_exceeded')
        return image
    def _read_image(self):
        try:
            image=self._image()
            canonical=self.bridge.call({'validateImage':image})
            if canonical!=image:fail('invalid_storage_state')
            return image
        except (KeyError,TypeError,ValueError,IndexError) as e:
            raise StoreError('invalid_storage_state',str(e)) from e
    def _apply(self,old,new):
        oldctx=dict(old['contexts']); oldactive={dumps(k):v for k,v in old['active']}
        oldentries={keytuple(k):v for k,v in old['entries']}; oldtx=dict(old['transactions'])
        for v,c in new['contexts']:
            if v not in oldctx:
                e=c['expected']
                self.db.execute('INSERT INTO context_versions VALUES (?,?,?,?,?)',
                    (v,e['contextId'],e['expectedSessionId'],e['expectedPolicyVersion'],dumps(c)))
            elif oldctx[v]!=c: fail('invalid_model_transition')
        for s,v in new['active']:
            st=tuple(s[x] for x in ('contextId','sessionId','policyVersion'))
            if dumps(s) not in oldactive:
                self.db.execute('INSERT INTO active_contexts VALUES (?,?,?,?)',(*st,v))
            elif oldactive[dumps(s)]!=v:
                self.db.execute('UPDATE active_contexts SET version_id=? WHERE context_id=? AND session_id=? AND policy_version=?',(v,*st))
        for k,e in new['entries']:
            kt=keytuple(k)
            if kt not in oldentries:
                self.db.execute("INSERT INTO challenge_entries VALUES (?,?,?,?,'ISSUED',NULL,NULL,NULL)",kt)
            elif oldentries[kt]!=e:
                r=e['consumed']['record']
                self.db.execute("UPDATE challenge_entries SET entry_state='CONSUMED',payload_digest=?,pinned_version=?,report=? WHERE context_id=? AND session_id=? AND policy_version=? AND challenge=?",
                    (bytes(r['payloadDigest']),r['pinnedContextVersion'],dumps(r['historicalReport']),*kt))
        for tx,t in new['transactions']:
            kind=tag(t); val=t[kind]; b=val['binding']
            if tx not in oldtx:
                self.db.execute("INSERT INTO transactions VALUES (?,?,?,?,?,?,'PENDING',NULL,NULL,NULL)",
                    (tx,*keytuple(b['key']),bytes(b['message'])))
            elif oldtx[tx]!=t:
                if kind=='aborted':
                    self.db.execute("UPDATE transactions SET tx_state='ABORTED',rejection_reason=? WHERE tx_id=?",(val['reason'],tx))
                elif kind=='committed':
                    order=len(new['accepted']) if val['kind']=='newAcceptance' else None
                    self.db.execute("UPDATE transactions SET tx_state='COMMITTED',acceptance_kind=?,acceptance_order=? WHERE tx_id=?",(val['kind'],order,tx))
                else: fail('invalid_model_transition')
    def _run(self,inp,*,write=True,precheck=None):
        with self._transaction(write):
            old=self._read_image()
            if precheck: precheck(old)
            try: answer=self.bridge.call(dict(image=old,input=inp))
            except (ValueError,RuntimeError,TimeoutError,OSError) as e: raise StoreError('model_failure',str(e)) from e
            if write: self._apply(old,answer['image'])
            # Compare normalized unordered maps; ghost log is ordered.
            actual=self._read_image()
            if normalize(actual)!=normalize(answer['image']): fail('refinement_mismatch')
            return answer['output']
    def install_context(self,version,config,cap):
        self._admin(cap)
        return self._run({'installContext':{'version':version,'cfg':config}})
    def issue(self,key,cap):
        self._admin(cap)
        return self._run({'issue':{'key':key}})
    def register(self,tx,request):
        b=self.bridge.call({'binding':request})
        def check(image):
            existing=dict(image['transactions']).get(tx)
            if existing and existing[tag(existing)]['binding']!=b: fail('transaction_binding_mismatch')
        return self._run({'beginTransaction':{'tx':tx,'q':request}},precheck=check)
    def commit_checked(self,tx,request):
        return self._run({'commit':{'tx':tx,'q':request}})
    def resolve(self,key,tx):
        def check(image):
            t=dict(image['transactions']).get(tx)
            if t and t[tag(t)]['binding']['key']!=key: fail('transaction_binding_mismatch')
        return self._run({'resolveTransaction':{'key':key,'tx':tx}},write=False,precheck=check)
    def lookup(self,key): return self._run({'lookup':{'key':key}},write=False)
    def abort_pending(self,key,tx,cap):
        self._admin(cap)
        with self._transaction(True):
            old=self._read_image(); t=dict(old['transactions']).get(tx)
            if t is None: return {'status':'transaction_not_found'}
            kind=tag(t); v=t[kind]
            if v['binding']['key']!=key: fail('transaction_binding_mismatch')
            if kind=='aborted': return {'status':'already_aborted','reason':v['reason']}
            if kind=='committed': return {'status':'already_committed','record':v['record'],'kind':v['kind']}
            answer=self.bridge.call(dict(image=old,input={'abort':{'tx':tx}}))
            self._apply(old,answer['image'])
            if normalize(self._read_image())!=normalize(answer['image']): fail('refinement_mismatch')
            return {'status':'aborted'}
    def inspect(self):
        with self._transaction(False): return self._read_image()

def normalize(image):
    return {k:(v if k=='accepted' else sorted(v,key=lambda x:dumps(x[0]))) for k,v in image.items()}
