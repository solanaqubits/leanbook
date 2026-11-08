import Verification.MasterSuiteComponents

open MlDsaRt1 MlDsaU128Conversion MlDsaCasmBlockSemantics

-- Exact composed contract through the public registry, with every premise retained.
example {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m)
    (ht : MlDsaRt1ArithmeticBlock.CheckedTrace m (MlDsaRt1ArithmeticBlock.arithmeticTrace a f))
    (hb : MlDsaRt1ArithmeticBlock.BitwiseAndAt m (m (a + -13) : Int))
    (hx : m (f + 25) < 2 ^ 64)
    (he : MlDsaRt1ConversionBlock.BlockExecution m (a + 9) f out) :
    out = .narrow (packRotl64_1 (m a)) :=
  MasterSuite.crypto_full_master_suite.{0, 0, 0, 0, 0, 0}.mldsa_cairo.arithmetic_narrow
    hc ht hb hx he
