import Verification.PrometheusCascadedFECBound
open scoped BigOperators
open PrometheusCascadedFECBound PrometheusFiniteBlockAudit

example : tail 240 205 (cascadeLaw (6664/10000) (10192/1000000)) < 12/1000000 :=
  rounded_iid_certificate
example : tail 240 205 (cascadeLaw (6664/10000) (34/3336)) < 12/1000000 :=
  historical_iid_certificate
example : (34/3336 : ℚ) ≠ 10192/1000000 := by norm_num
example (crc : Bool → Bool) : crcAccept crc (tagged crc true) ∧
    tagged crc true ≠ tagged crc false := wrong_valid_frame crc false true (by decide)
example (m : Noise → ℚ) (hm : ∀ x, 0 ≤ m x) (bad : (Fin 240 → Noise) → Prop)
    (hc : ∀ w, weight w ≤ 204 → ¬ bad w) :
    (∑ w, productMass m w * indicator (bad w)) ≤
      (m .correct + m .erased*2 + m .flipped*2^2)^240/2^205 :=
  failure_bound 240 m hm bad hc 2 (by norm_num)
