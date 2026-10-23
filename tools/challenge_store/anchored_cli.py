"""Explicit pinned-Witness CLI for a previously provisioned trusted-host registry.

No plain Store fallback, initialization, enrollment, cancellation or anchor reset.
This is not a remote service or proof of production provider qualification.
"""
import argparse
from pathlib import Path

from .anchor import AnchoredStore
from .bridge import dumps, loads
from .files import FilePackage, read_bounded, submit_files
from .store import StoreError
from .witness_config import DeploymentError, load_deployment
from .witness_https import WitnessTransportError

MAX_ENVELOPE_BYTES = 16 * 1024


def _fields(obj, names):
    if type(obj) is not dict or set(obj) != set(names):
        raise ValueError('invalid envelope fields')


def _identifier(value):
    if (type(value) is not str or not value or len(value.encode('utf-8')) > 256
            or any(ord(c) < 32 or ord(c) == 127 for c in value)):
        raise ValueError('invalid identifier')
    return value


def _key(key):
    _fields(key, ('scope', 'challenge'))
    _fields(key['scope'], ('contextId', 'sessionId', 'policyVersion'))
    for value in key['scope'].values():
        _identifier(value)
    if type(key['challenge']) is not list or any(type(v) is not int or not 0 <= v <= 255
                                              for v in key['challenge']):
        raise ValueError('invalid challenge bytes')
    return key


def _input(args):
    if not args.db.is_absolute() or '..' in args.db.parts:
        raise ValueError('absolute database path required')
    if args.operation == 'inspect':
        return {}
    raw = read_bounded(args.input, MAX_ENVELOPE_BYTES)
    obj = loads(raw.decode('utf-8'))
    if args.operation == 'lookup':
        _fields(obj, ('key',))
    elif args.operation == 'resolve':
        _fields(obj, ('key', 'txId'))
    else:
        _fields(obj, ('txId',))
        _identifier(args.context_version)
    if 'key' in obj:
        _key(obj['key'])
    if 'txId' in obj:
        _identifier(obj['txId'])
    return obj


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--db', required=True, type=Path)
    parser.add_argument('--config', required=True)
    parser.add_argument('--config-sha256', required=True)
    commands = parser.add_subparsers(dest='operation', required=True)
    commands.add_parser('inspect')
    for command in ('lookup', 'resolve', 'submit-files'):
        sub = commands.add_parser(command)
        sub.add_argument('--input', required=True, type=Path)
        if command == 'submit-files':
            sub.add_argument('--context-version', required=True)
            for name in ('manifest', 'signature', 'snapshot', 'profile'):
                sub.add_argument('--' + name, required=True, type=Path)
    args = parser.parse_args(argv)
    envelope = dict(schema='anchored-store-cli/v1', operation=args.operation,
                    protection='anchored', authorization='blocked',
                    external_service_qualified=False)
    try:
        obj = _input(args)
        deployment = load_deployment(args.config, expected_sha256=args.config_sha256)
        witness = deployment.make_witness()
        # No Controller capability is constructed; administrative operations stay API-only.
        with AnchoredStore(args.db, store_id=deployment.store_id, witness=witness) as store:
            if args.operation == 'inspect':
                result = store.inspect()
            elif args.operation == 'lookup':
                result = store.lookup(obj['key'])
            elif args.operation == 'resolve':
                result = store.resolve(obj['key'], obj['txId'])
            else:
                package = FilePackage(args.manifest, args.signature, args.snapshot, args.profile)
                result = submit_files(store, obj['txId'], args.context_version, package)
        envelope.update(status='completed', result=result,
                        deployment_id=deployment.deployment_id, revision=deployment.revision,
                        store_id=deployment.store_id,
                        configuration_sha256=deployment.configuration_sha256)
        code = 0
    except (StoreError, DeploymentError, WitnessTransportError) as error:
        # An error may follow a durable local or external write. Never claim rollback.
        envelope.update(status='error', error=error.code)
        code = 2
    except (OSError, ValueError, TypeError, KeyError, RecursionError, OverflowError, RuntimeError):
        # No exception text, credential paths, request bodies or backend internals.
        envelope.update(status='error', error='input_or_runtime_failure')
        code = 2
    print(dumps(envelope))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
