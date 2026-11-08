/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MlDsaCasmBlockSemantics
import Verification.MlDsaCasmWitnessLifting
import Verification.MlDsaRt1ArithmeticBlock

/-! Registry for the pinned, flat immutable-memory block model. These obligations
retain their entry, exit, range-check and input-binding assumptions. They do not
assert correspondence to a real Cairo VM, compiler or complete signature verifier. -/
namespace MlDsaCairoBlockSuite

open MlDsaRt1 MlDsaU128Conversion MlDsaCasmBlockSemantics
open MlDsaCasmBlockSemantics.TraceCompleteness

structure CairoBlockSuite : Prop where
  rotation (w : Nat) (hw : w < 2 ^ 128) :
    rt1FieldExpr w rt1Mask = packRotl64_1 w
  trace_classification {m : Memory} {a f : Int} {trace : List State}
    (hc : Canonical m) (hstart : trace.head? = some (frame a f 1274 0))
    (ht : CheckedTrace m trace) (he : EndsAtExit trace) :
    trace = narrowTrace a f ∨
    trace = widePrefix a f ++ (wideEqualTail a f).tail ∨
    trace = widePrefix a f ++ (wideLessTail a f).tail
  conversion {m : Memory} {a f : Int} {trace : List State}
    (hc : Canonical m) (hstart : trace.head? = some (frame a f 1274 0))
    (ht : CheckedTrace m trace) (he : EndsAtExit trace)
    (hrc : TraceRangeChecks m f trace) :
    ConversionChecks (m (a + -1)) (traceResult m a trace)
  rt1_narrow {m : Memory} {a f : Int} {trace : List State}
    (hc : Canonical m) (hstart : trace.head? = some (frame a f 1274 0))
    (ht : CheckedTrace m trace) (he : EndsAtExit trace)
    (hrc : TraceRangeChecks m f trace) {w : Nat} (hw : w < 2 ^ 128)
    (hin : m (a + -1) = rt1FieldExpr w rt1Mask) :
    traceResult m a trace = .narrow (packRotl64_1 w)

  /-- New window only: explicit arithmetic steps, AND relation, lane bound and conversion. -/
  arithmetic_narrow {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m)
    (ht : MlDsaRt1ArithmeticBlock.CheckedTrace m (MlDsaRt1ArithmeticBlock.arithmeticTrace a f))
    (hb : MlDsaRt1ArithmeticBlock.BitwiseAndAt m (m (a + -13) : Int))
    (hx : m (f + 25) < 2 ^ 64)
    (he : MlDsaRt1ConversionBlock.BlockExecution m (a + 9) f out) :
    out = .narrow (packRotl64_1 (m a))

theorem verification_suite : CairoBlockSuite := {
  arithmetic_narrow := MlDsaRt1ArithmeticBlock.arithmetic_conversion_narrow
  rotation := @rt1FieldExpr_eq_packRotl64_1
  trace_classification := trace_classification
  conversion := trace_to_conversionChecks
  rt1_narrow := trace_rt1_narrow
}

end MlDsaCairoBlockSuite
