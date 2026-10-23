import Verification.MasterSuite

open DataAvailabilitySamplingContract

example : DataAvailabilitySamplingSuite := by
  have r := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact r.crypto_suite.data_availability

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    DataAvailabilitySamplingSuite := r.crypto_full_suite.data_availability

example (r : MasterSuite.CryptoFullSuite) :
    DataAvailabilitySamplingSuite := r.data_availability

example (r : MasterSuite.CryptoFullSuite) (p : RSBlockParams)
    (a : Finset (Fin p.n)) (S : ℕ) (h : a.card < p.k) :
    samplingSuccessProbability a S ≤ maxDeceptionProbability p S :=
  r.data_availability.ceiling p a S h

example (r : MasterSuite.CryptoFullSuite) (p : RSBlockParams) :
    maxDeceptionProbability p 20 < 1 / 1000000 := r.data_availability.twenty p

example (r : MasterSuite.CryptoFullSuite) (n S : ℕ) (a : Finset (Fin n)) :
    Fintype.card (SuccessfulTrace a S) = a.card ^ S :=
  r.data_availability.trace_count n S a

example (r : MasterSuite.CryptoFullSuite) (n S : ℕ) (a : Finset (Fin n)) :
    samplingSuccessProbability a S = ((a.card : ℚ) / (n : ℚ)) ^ S :=
  r.data_availability.probability n S a

example (r : MasterSuite.CryptoFullSuite) (params : RSBlockParams)
    (a : Finset (Fin params.n)) (nodes values : Fin params.n → ℚ)
    (hd : Set.InjOn nodes a) (p : Polynomial ℚ) (hp : p.degree < params.k)
    (ha : ∀ i ∈ a, values i = p.eval (nodes i))
    (hr : isRecoverable params (stateOfAvailable params a)) :
    Lagrange.interpolate a nodes values = p :=
  r.data_availability.polynomial_reconstruction ℚ params a nodes values hd p hp ha hr
