import unittest
from tools.lean_fixture_format import wrap_source

class FixtureFormatTests(unittest.TestCase):
    def test_kernel_modifier_stays_with_tactic(self):
        text='example : '+('longArgumentName '*6)+'= 0 := by decide +kernel\n'
        value=wrap_source(text)
        self.assertIn(':= by decide +kernel',value)
        self.assertEqual(''.join(text.split()),''.join(value.split()))
    def test_string_bytes_preserved(self):
        text='def payload := "'+('a'*150)+'"\n'
        value=wrap_source(text)
        self.assertIn('"'+('a'*150)+'"',value)
    def test_heartbeat_scope_and_reason(self):
        text='set_option maxHeartbeats 0\nexample : True := by trivial\n'
        value=wrap_source(text)
        self.assertIn('set_option maxHeartbeats 0 in\n--',value)
        self.assertEqual(wrap_source(value),value)
    def test_registry_alias_is_same_expression(self):
        registry='MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}'
        text='import Verification.MasterSuite\nexample : T := '+registry+'.distributed_suite.actuator_arbitration.history\n'
        value=wrap_source(text)
        self.assertIn('private abbrev migrationRegistry :=\n  '+registry,value)
        self.assertIn('migrationRegistry.distributed_suite.actuator_arbitration.history',value)

    def test_mixed_resource_budgets_require_explicit_review(self):
        source = ("set_option maxHeartbeats 800000\nexample : True := by trivial\n"
                  "set_option maxHeartbeats 1600000\nexample : True := by trivial\n")
        with self.assertRaisesRegex(ValueError, "Multiple heartbeat budgets"):
            wrap_source(source)
