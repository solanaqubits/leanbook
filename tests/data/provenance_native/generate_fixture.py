"""Optional regeneration of a public-test-key fixture, never used during replay tests.
Uses cryptography/OpenSSL independently of the libsodium verifier under test.
The seed is the published RFC8032 test1 key, never a production credential.
"""
import hashlib
import json
from pathlib import Path
from cryptography import __version__
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.backends.openssl.backend import backend


def nat(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)


def blob(b):
    return nat(len(b)) + b


def text(s):
    return blob(s.encode('utf-8'))


def main():
    snapshot, profile = bytes([1,2,3]), bytes([4,5])
    strings = ['fixture-signer','rfc8032-key1','quota-auditor','native-test-session']
    body = b''.join(map(text,strings)) + blob(bytes([16,32,48])) + text('native-profile-v1')
    for b in [snapshot,profile]:
        body += nat(len(b)) + blob(hashlib.sha256(b).digest())
    body += nat(3)+nat(1)+bytes([1])+nat(1)+nat(2)+text('native-context')
    body += bytes([1])+text('test-clock')+text('ticks')+bytes([1])+nat(3)
    message = b'SIMLAB_PROVENANCE_V1_SHA256_ED25519:' + b'QPM\x01' + body
    private = Ed25519PrivateKey.from_private_bytes(bytes.fromhex(
        '9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60'))
    signature = private.sign(message)
    private.public_key().verify(signature,message)
    result = dict(kind='synthetic-native-conformance-only',generator='cryptography '+__version__,
                  openssl=backend.openssl_version_text(),message=message.hex(),signature=signature.hex(),
                  public_key=private.public_key().public_bytes_raw().hex(),snapshot=snapshot.hex(),profile=profile.hex(),
                  snapshot_digest=hashlib.sha256(snapshot).hexdigest(),profile_digest=hashlib.sha256(profile).hexdigest())
    destination=Path(__file__).with_name('integration.json')
    with destination.open('x') as f:json.dump(result,f,indent=2);f.write('\n')


if __name__ == '__main__':
    main()
