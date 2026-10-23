"""Explicit, independently pinned local Witness configuration and read-only probe.

POSIX trusted-host profile. A successful probe is an observation, never production
qualification, enrollment, a comparison against a local DB, or permission to write.
"""
import argparse
from dataclasses import dataclass, field
import hashlib
import hmac
import os
from pathlib import Path
import re
import stat

from .bridge import dumps, loads
from .anchor import Ready, Prepared
from .witness_https import HTTPSWitness, WitnessTLSConfig, WitnessTransportError

SCHEMA = 'witness-deployment/v1'
MAX_CONFIG_BYTES = 16 * 1024
MAX_CREDENTIAL_BYTES = 64 * 1024


class DeploymentError(RuntimeError):
    """Stable public code; diagnostics never include credential paths or contents."""
    def __init__(self, code):
        self.code = code
        super().__init__(code)


def _path(value):
    if (type(value) is not str or not value or len(value.encode('utf-8')) > 4096
            or '\x00' in value or not Path(value).is_absolute()
            or '..' in Path(value).parts):
        raise DeploymentError('invalid_path')
    return Path(value)


def _file(path, limit, *, secret=False):
    """Bounded regular-file read; no final symlink, foreign owner or unsafe mode.

    Parent directories and later OpenSSL path opens remain trusted-host premises.
    These checks are not a defense against root/owner compromise or hostile ACLs.
    """
    if os.name != 'posix' or not hasattr(os, 'O_NOFOLLOW'):
        raise DeploymentError('unsupported_platform')
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        with os.fdopen(fd, 'rb') as stream:
            info = os.fstat(stream.fileno())
            if not stat.S_ISREG(info.st_mode):
                raise DeploymentError('not_regular_file')
            if info.st_uid not in (0, os.geteuid()):
                raise DeploymentError('untrusted_file_owner')
            if info.st_mode & (0o077 if secret else 0o022):
                raise DeploymentError('unsafe_file_permissions')
            if info.st_size > limit:
                raise DeploymentError('file_limit_exceeded')
            raw = stream.read(limit + 1)
            if len(raw) > limit:
                raise DeploymentError('file_limit_exceeded')
            return raw
    except OSError:
        raise DeploymentError('file_access_failed') from None


def _fields(obj, names):
    if type(obj) is not dict or set(obj) != set(names):
        raise DeploymentError('invalid_config_schema')


def _identity(value):
    if (type(value) is not str or not value or len(value.encode('utf-8')) > 256
            or any(ord(c) < 32 or ord(c) == 127 for c in value)):
        raise DeploymentError('invalid_identity')
    return value


@dataclass(frozen=True)
class WitnessDeployment:
    deployment_id: str
    revision: str
    store_id: str
    configuration_sha256: str
    tls: WitnessTLSConfig = field(repr=False)

    def make_witness(self):
        # Recheck on every construction; OpenSSL opens only these explicit paths.
        _file(self.tls.ca_file, MAX_CREDENTIAL_BYTES)
        _file(self.tls.client_cert, MAX_CREDENTIAL_BYTES)
        _file(self.tls.client_key, MAX_CREDENTIAL_BYTES, secret=True)
        return HTTPSWitness(self.tls)

    def report(self, status):
        return dict(schema='witness-preflight/v1', status=status,
                    deployment_id=self.deployment_id, revision=self.revision,
                    store_id=self.store_id, server_id=self.tls.server_id,
                    configuration_sha256=self.configuration_sha256,
                    external_service_qualified=False, authorization='blocked')


def load_deployment(path, *, expected_sha256):
    """Pin exact config bytes against an independently supplied expected digest.

    No environment interpolation/discovery, TOFU, relative credential paths or
    provider-approved flags. Whitespace is allowed in config JSON, but affects pin.
    """
    if type(expected_sha256) is not str or not re.fullmatch('[0-9a-f]{64}', expected_sha256):
        raise DeploymentError('invalid_configuration_pin')
    try:
        config_path = _path(os.fspath(path))
    except (UnicodeError, ValueError, TypeError):
        raise DeploymentError('invalid_path') from None
    raw = _file(config_path, MAX_CONFIG_BYTES)
    digest = hashlib.sha256(raw).hexdigest()
    if not hmac.compare_digest(digest, expected_sha256):
        raise DeploymentError('configuration_pin_mismatch')
    try:
        obj = loads(raw.decode('utf-8'))
        _fields(obj, ('schema', 'deployment_id', 'revision', 'store_id', 'transport'))
        if obj['schema'] != SCHEMA:
            raise DeploymentError('invalid_config_schema')
        for name in ('deployment_id', 'revision', 'store_id'):
            _identity(obj[name])
        t = obj['transport']
        _fields(t, ('host', 'port', 'server_id', 'ca_file', 'client_cert', 'client_key',
                    'server_cert_sha256', 'timeout_seconds'))
        _identity(t['server_id'])
        cfg = WitnessTLSConfig(**{**t, **{k: _path(t[k]) for k in
                                         ('ca_file', 'client_cert', 'client_key')}})
        deployment = WitnessDeployment(obj['deployment_id'], obj['revision'],
                                       obj['store_id'], digest, cfg)
        # Checks scalar transport fields and parses TLS credentials without network.
        deployment.make_witness()
        return deployment
    except (ValueError, UnicodeError, TypeError, RecursionError, OverflowError):
        raise DeploymentError('invalid_config_schema') from None


def probe(deployment):
    """One authenticated read only. No Store/SQLite open, CAS or recovery action."""
    head = deployment.make_witness().read(deployment.store_id)
    if head is None:
        report = deployment.report('store_not_provisioned')
    elif type(head) is Prepared:
        report = deployment.report('prepared_head_observed')
        # No recovery token in diagnostics; use the existing recovery API separately.
        report['head'] = dict(kind='prepared', epoch=head.epoch, digest=head.digest)
    elif type(head) is Ready:
        report = deployment.report('ready_head_observed')
        report['head'] = dict(kind='ready', epoch=head.epoch, digest=head.digest)
    else:
        raise DeploymentError('invalid_head')
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('check-config', 'probe'))
    parser.add_argument('--config', required=True, help='absolute protected JSON file path')
    parser.add_argument('--config-sha256', required=True, help='independently trusted exact file digest')
    args = parser.parse_args(argv)
    try:
        deployment = load_deployment(args.config, expected_sha256=args.config_sha256)
        report = (deployment.report('configuration_valid') if args.command == 'check-config'
                  else probe(deployment))
        code = 0 if report['status'] in ('configuration_valid', 'ready_head_observed') else 3
    except (DeploymentError, WitnessTransportError) as error:
        report = dict(schema='witness-preflight/v1', status='refused', error=error.code,
                      external_service_qualified=False, authorization='blocked')
        code = 1
    print(dumps(report))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
