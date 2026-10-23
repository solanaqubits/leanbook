#include <sqlite3.h>
#include <stdio.h>
#include <stddef.h>
int main(void){
printf("sqlite3_file %zu %zu\n",sizeof(sqlite3_file),_Alignof(sqlite3_file));
printf("sqlite3_io_methods %zu %zu\n",sizeof(sqlite3_io_methods),_Alignof(sqlite3_io_methods));
printf("sqlite3_vfs %zu %zu\n",sizeof(sqlite3_vfs),_Alignof(sqlite3_vfs));
printf("sqlite3_mem_methods %zu %zu\n",sizeof(sqlite3_mem_methods),_Alignof(sqlite3_mem_methods));
printf("sqlite3_module %zu %zu\n",sizeof(sqlite3_module),_Alignof(sqlite3_module));
printf("sqlite3_index_info %zu %zu\n",sizeof(sqlite3_index_info),_Alignof(sqlite3_index_info));
printf("sqlite3_vtab %zu %zu\n",sizeof(sqlite3_vtab),_Alignof(sqlite3_vtab));
printf("sqlite3_vtab_cursor %zu %zu\n",sizeof(sqlite3_vtab_cursor),_Alignof(sqlite3_vtab_cursor));
printf("sqlite3_mutex_methods %zu %zu\n",sizeof(sqlite3_mutex_methods),_Alignof(sqlite3_mutex_methods));
printf("sqlite3_pcache_page %zu %zu\n",sizeof(sqlite3_pcache_page),_Alignof(sqlite3_pcache_page));
printf("sqlite3_pcache_methods2 %zu %zu\n",sizeof(sqlite3_pcache_methods2),_Alignof(sqlite3_pcache_methods2));
printf("sqlite3_snapshot %zu %zu\n",sizeof(sqlite3_snapshot),_Alignof(sqlite3_snapshot));
printf("vfs.xOpen %zu\n",offsetof(sqlite3_vfs,xOpen));
printf("io.xShmLock %zu\n",offsetof(sqlite3_io_methods,xShmLock));
printf("io.xUnfetch %zu\n",offsetof(sqlite3_io_methods,xUnfetch));
return 0;}
