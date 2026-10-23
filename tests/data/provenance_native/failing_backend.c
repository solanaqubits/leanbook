/* Deliberately non-cryptographic shared-library fault fixture. Never production. */
#include <stddef.h>
#ifndef FAILURE
#define FAILURE 1
#endif
int sodium_init(void) { return FAILURE == 1 ? -1 : 0; }
const char *sodium_version_string(void) { return "1.0.18"; }
size_t crypto_sign_publickeybytes(void) { return FAILURE == 4 ? 31 : 32; }
size_t crypto_sign_bytes(void) { return 64; }
size_t crypto_hash_sha256_bytes(void) { return 32; }
int crypto_sign_verify_detached(const unsigned char *s, const unsigned char *m,
    unsigned long long n, const unsigned char *k) {
    (void)s; (void)m; (void)n; (void)k; return FAILURE == 3 ? 17 : -1;
}
#ifndef OMIT_HASH
int crypto_hash_sha256(unsigned char *out, const unsigned char *m, unsigned long long n) {
    (void)out; (void)m; (void)n; return -1;
}
#endif
