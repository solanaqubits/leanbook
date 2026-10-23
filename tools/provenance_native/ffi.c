/* Explicit effectful Lean IO bridge. No signing API and no pure externs. */
#include <lean/lean.h>
#include <dlfcn.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>

typedef struct {
    void *handle;
    int (*init)(void);
    const char *(*version)(void);
    size_t (*pkbytes)(void);
    size_t (*sigbytes)(void);
    size_t (*hashbytes)(void);
    int (*verify)(const unsigned char *, const unsigned char *, unsigned long long,
                  const unsigned char *);
    int (*hash)(unsigned char *, const unsigned char *, unsigned long long);
} backend;

static int close_backend(backend *b) {
    int result = b->handle != NULL ? dlclose(b->handle) : 0;
    b->handle = NULL;
    return result == 0;
}
/* POSIX dlsym function pointer conversion, checked before use. */
#define LOAD(field, symbol) do { \
    void *sym = dlsym(b->handle, symbol); \
    if (sym == NULL) { close_backend(b); return 0; } \
    _Static_assert(sizeof(b->field) == sizeof(sym), "POSIX function pointer ABI"); \
    memcpy(&b->field, &sym, sizeof(sym)); \
} while (0)

static int open_backend(backend *b, b_lean_obj_arg path, b_lean_obj_arg expected) {
    memset(b, 0, sizeof(*b));
    /* No loader search path and no embedded-NUL truncation. */
    const char *p = lean_string_cstr(path);
    const char *v = lean_string_cstr(expected);
    if (p[0] != '/' || strlen(p) + 1 != lean_string_size(path) ||
        strlen(v) + 1 != lean_string_size(expected)) return 0;
    b->handle = dlopen(p, RTLD_NOW | RTLD_LOCAL);
    if (b->handle == NULL) return 0;
    LOAD(init, "sodium_init");
    LOAD(version, "sodium_version_string");
    LOAD(pkbytes, "crypto_sign_publickeybytes");
    LOAD(sigbytes, "crypto_sign_bytes");
    LOAD(hashbytes, "crypto_hash_sha256_bytes");
    LOAD(verify, "crypto_sign_verify_detached");
    LOAD(hash, "crypto_hash_sha256");
    const char *actual = b->version();
    if (actual == NULL || strcmp(actual, v) != 0 || b->pkbytes() != 32 ||
        b->sigbytes() != 64 || b->hashbytes() != 32 || b->init() < 0) {
        close_backend(b); return 0;
    }
    return 1;
}

/* An IO UInt8: 0 invalid, 1 valid, 2 controlled backend failure. */
LEAN_EXPORT lean_obj_res provenance_verify_io(b_lean_obj_arg path, b_lean_obj_arg version,
    b_lean_obj_arg key, b_lean_obj_arg message, b_lean_obj_arg signature) {
    if (lean_sarray_size(key) != 32 || lean_sarray_size(signature) != 64 ||
        lean_sarray_size(message) > ULLONG_MAX)
        return lean_io_result_mk_ok(lean_box(2));
    backend b;
    if (!open_backend(&b, path, version)) return lean_io_result_mk_ok(lean_box(2));
    int rc = b.verify(lean_sarray_cptr(signature), lean_sarray_cptr(message),
                     (unsigned long long)lean_sarray_size(message), lean_sarray_cptr(key));
    if (!close_backend(&b)) return lean_io_result_mk_ok(lean_box(2));
    return lean_io_result_mk_ok(lean_box(rc == 0 ? 1 : rc == -1 ? 0 : 2));
}

/* IO ByteArray: empty = controlled failure; exactly32 bytes = success.
Lean runtime allocation failures may abort and are deliberately not claimed caught. */
LEAN_EXPORT lean_obj_res provenance_sha256_io(b_lean_obj_arg path, b_lean_obj_arg version,
    b_lean_obj_arg message) {
    unsigned char digest[32];
    backend b;
    int ok = 0;
    if (lean_sarray_size(message) <= ULLONG_MAX && open_backend(&b, path, version)) {
        ok = b.hash(digest, lean_sarray_cptr(message),
                    (unsigned long long)lean_sarray_size(message)) == 0;
        if (!close_backend(&b)) ok = 0;
    }
    lean_object *result = lean_alloc_sarray(1, ok ? 32 : 0, ok ? 32 : 0);
    if (ok) memcpy(lean_sarray_cptr(result), digest, 32);
    return lean_io_result_mk_ok(result);
}
