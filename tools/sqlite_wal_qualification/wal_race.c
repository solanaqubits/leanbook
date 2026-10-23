#define _GNU_SOURCE
#include <sqlite3.h>
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#define APIS(X) X(open_v2) X(close) X(exec) X(free) X(errmsg) X(vfs_find) X(vfs_register) X(wal_checkpoint_v2) X(prepare_v2) X(step) X(column_text) X(finalize) X(libversion) X(sourceid)
#define DECL(n) static __typeof__(sqlite3_##n) *f_##n;
APIS(DECL)
static sqlite3_vfs *under;
static sqlite3 *writer;
static int armed=0, fired=0;
typedef struct {sqlite3_file base;sqlite3_file *real;int main_db;} Wrap;
static int query(sqlite3*d,const char*s){char *e=0;int rc=f_exec(d,s,0,0,&e);if(rc){fprintf(stderr,"SQL %d: %s [%s]\n",rc,e?e:"",s);f_free(e);exit(2);}return rc;}
static sqlite3_file *real(sqlite3_file*p){return ((Wrap*)p)->real;}
static int cClose(sqlite3_file*p){sqlite3_file*q=real(p);int rc=q->pMethods->xClose(q);free(q);return rc;}
static int cRead(sqlite3_file*p,void*b,int n,sqlite3_int64 o){sqlite3_file*q=real(p);return q->pMethods->xRead(q,b,n,o);}
static int cWrite(sqlite3_file*p,const void*b,int n,sqlite3_int64 o){sqlite3_file*q=real(p);return q->pMethods->xWrite(q,b,n,o);}
static int cTruncate(sqlite3_file*p,sqlite3_int64 n){sqlite3_file*q=real(p);return q->pMethods->xTruncate(q,n);}
static int cSync(sqlite3_file*p,int n){sqlite3_file*q=real(p);return q->pMethods->xSync(q,n);}
static int cSize(sqlite3_file*p,sqlite3_int64*n){sqlite3_file*q=real(p);return q->pMethods->xFileSize(q,n);}
static int cLock(sqlite3_file*p,int n){sqlite3_file*q=real(p);return q->pMethods->xLock(q,n);}
static int cUnlock(sqlite3_file*p,int n){sqlite3_file*q=real(p);return q->pMethods->xUnlock(q,n);}
static int cReserved(sqlite3_file*p,int*n){sqlite3_file*q=real(p);return q->pMethods->xCheckReservedLock(q,n);}
static int cControl(sqlite3_file*p,int n,void*b){sqlite3_file*q=real(p);return q->pMethods->xFileControl(q,n,b);}
static int cSector(sqlite3_file*p){sqlite3_file*q=real(p);return q->pMethods->xSectorSize(q);}
static int cDevice(sqlite3_file*p){sqlite3_file*q=real(p);return q->pMethods->xDeviceCharacteristics(q);}
static int cMap(sqlite3_file*p,int i,int n,int e,void volatile**b){sqlite3_file*q=real(p);return q->pMethods->xShmMap(q,i,n,e,b);}
static int cShmLock(sqlite3_file*p,int o,int n,int f){sqlite3_file*q=real(p);return q->pMethods->xShmLock(q,o,n,f);}
static void cBarrier(sqlite3_file*p){sqlite3_file*q=real(p);q->pMethods->xShmBarrier(q);}
static int cUnmap(sqlite3_file*p,int n){sqlite3_file*q=real(p);return q->pMethods->xShmUnmap(q,n);}
static int cFetch(sqlite3_file*p,sqlite3_int64 o,int n,void**b){sqlite3_file*q=real(p);return q->pMethods->xFetch(q,o,n,b);}
static int cUnfetch(sqlite3_file*p,sqlite3_int64 o,void*b){
 sqlite3_file*q=real(p);int rc=q->pMethods->xUnfetch(q,o,b);
 if(armed && ((Wrap*)p)->main_db && o==0 && b==0){
  armed=0;fired++;puts("BARRIER: checkpoint read cached header; writer resets WAL now");
  query(writer,"UPDATE t1 SET b=printf('%0600d',a+2000) WHERE a<5");
  puts("WRITER: reset transaction committed");
 }
 return rc;
}
static const sqlite3_io_methods methods={3,cClose,cRead,cWrite,cTruncate,cSync,cSize,cLock,cUnlock,cReserved,cControl,cSector,cDevice,cMap,cShmLock,cBarrier,cUnmap,cFetch,cUnfetch};
static int cOpen(sqlite3_vfs*v,const char*z,sqlite3_file*p,int flags,int*out){
 (void)v;Wrap*w=(Wrap*)p;memset(w,0,sizeof(*w));w->real=calloc(1,under->szOsFile);if(!w->real)return SQLITE_NOMEM;
 int rc=under->xOpen(under,z,w->real,flags,out);if(rc){free(w->real);return rc;}
 if(w->real->pMethods->iVersion<3){fprintf(stderr,"VFS version unsupported\n");exit(2);}
 w->main_db=!!(flags&SQLITE_OPEN_MAIN_DB);w->base.pMethods=&methods;return SQLITE_OK;
}
static char *scalar(sqlite3*d,const char*sql){sqlite3_stmt*s=0;int rc=f_prepare_v2(d,sql,-1,&s,0);if(rc){return strdup(f_errmsg(d));}rc=f_step(s);char*out=strdup(rc==SQLITE_ROW?(const char*)f_column_text(s,0):f_errmsg(d));f_finalize(s);return out;}
static void checkpoint(sqlite3*d,const char*label){int n=-1,k=-1;int rc=f_wal_checkpoint_v2(d,0,SQLITE_CHECKPOINT_PASSIVE,&n,&k);printf("%s rc=%d frames=%d backfilled=%d\n",label,rc,n,k);if(rc!=SQLITE_OK)exit(2);}
int main(int argc,char**argv){
 if(argc!=4){fprintf(stderr,"usage: harness ABS_LIBRARY DB_PATH inject|plain\n");return 2;}
 void*h=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL);if(!h){fprintf(stderr,"%s\n",dlerror());return 2;}
 #define LOAD(n) *(void**)(&f_##n)=dlsym(h,"sqlite3_"#n);if(!f_##n){fprintf(stderr,"missing %s\n",#n);return 2;}
 APIS(LOAD)
 Dl_info di;dladdr((void*)f_open_v2,&di);printf("loaded=%s version=%s source=%s\n",di.dli_fname,f_libversion(),f_sourceid());
 under=f_vfs_find(0);sqlite3_vfs shim=*under;shim.zName="external-race-shim";shim.szOsFile=sizeof(Wrap);shim.xOpen=cOpen;if(f_vfs_register(&shim,0))return 2;
 if(access(argv[2],F_OK)==0){fprintf(stderr,"refuse existing database\n");return 2;}
 if(f_open_v2(argv[2],&writer,SQLITE_OPEN_READWRITE|SQLITE_OPEN_CREATE,under->zName))return 2;
 query(writer,"PRAGMA page_size=1024; PRAGMA auto_vacuum=0; PRAGMA journal_mode=WAL; PRAGMA synchronous=FULL; PRAGMA wal_autocheckpoint=0; CREATE TABLE t1(a INTEGER PRIMARY KEY,b); WITH RECURSIVE s(i) AS (VALUES(1) UNION ALL SELECT i+1 FROM s WHERE i<20) INSERT INTO t1 SELECT i,printf('%0600d',i) FROM s; CREATE INDEX i1 ON t1(b);");
 sqlite3*ck=0;if(f_open_v2(argv[2],&ck,SQLITE_OPEN_READWRITE,"external-race-shim"))return 2;
 query(ck,"PRAGMA wal_autocheckpoint=0; PRAGMA synchronous=FULL; SELECT count(*) FROM t1;");
 checkpoint(writer,"first");
 query(writer,"UPDATE t1 SET b=printf('%0600d',a+1000)");checkpoint(writer,"second");
 armed=!strcmp(argv[3],"inject");checkpoint(ck,"raced");
 if(!strcmp(argv[3],"inject")&&fired!=1){fprintf(stderr,"injector did not fire exactly once\n");return 2;}
 if(!strcmp(argv[3],"plain"))query(writer,"UPDATE t1 SET b=printf('%0600d',a+2000) WHERE a<5");
 query(writer,"UPDATE t1 SET b=printf('%0600d',a+3000) WHERE a>=5");checkpoint(writer,"final");
 char*integrity=scalar(writer,"PRAGMA integrity_check");char*count=scalar(writer,"SELECT count(*) FROM t1 NOT INDEXED WHERE b=printf('%0600d',a+CASE WHEN a<5 THEN 2000 ELSE 3000 END)");
 printf("integrity=%s exact_rows=%s fired=%d\n",integrity,count,fired);
 int good=!strcmp(integrity,"ok")&&!strcmp(count,"20");free(integrity);free(count);f_close(ck);f_close(writer);
 sqlite3*again=0;int rc=f_open_v2(argv[2],&again,SQLITE_OPEN_READONLY,under->zName);if(rc)return 2;
 integrity=scalar(again,"PRAGMA integrity_check");count=scalar(again,"SELECT count(*) FROM t1 NOT INDEXED WHERE b=printf('%0600d',a+CASE WHEN a<5 THEN 2000 ELSE 3000 END)");
 printf("reopen_integrity=%s reopen_exact_rows=%s\n",integrity,count);good=good&&!strcmp(integrity,"ok")&&!strcmp(count,"20");free(integrity);free(count);f_close(again);
 return good?0:1;
}
