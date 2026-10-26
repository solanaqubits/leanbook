"""Error-specific checks for deliberate kernel-reduction failures."""
import json

def assert_reduction_rejected(test, result):
    test.assertEqual(result.returncode, 1, result.stdout + result.stderr)
    errors=[]
    for line in result.stdout.splitlines():
        try: message=json.loads(line)
        except ValueError: continue
        if isinstance(message,dict) and message.get('severity')=='error':
            errors.append(message.get('data',''))
    test.assertTrue(errors, result.stdout + result.stderr)
    test.assertTrue(all('Tactic `rfl` failed' in error for error in errors), errors)


def checked_eval_output(test, result):
    """Keep exact #eval values; separate the known informational hash-command note.

    This does not suppress any compiler warning/error or discard unknown output.
    The consumers compare all remaining values to independent expected literals.
    """
    test.assertEqual(result.returncode, 0, result.stdout + result.stderr)
    note = "`#`-commands, such as '#eval', are not allowed in 'Mathlib' [linter.hashCommand]"
    values = []
    for line in result.stdout.splitlines():
        message = json.loads(line)
        test.assertIsInstance(message, dict)
        test.assertEqual(message.get('severity'), 'information', message)
        test.assertIsInstance(message.get('data'), str)
        if message['data'] != note:
            values.append(message['data'])
    return '\n'.join(values)
