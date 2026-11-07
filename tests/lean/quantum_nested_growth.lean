import Verification.QuantumNestedRepeater
open QuantumNestedRepeater QuantumCentralDepolarization QuantumRepeaterChain
open QuantumHeterogeneousBBPSSW

example (m : ℕ) (w : Visibility) (h : w.val < (nestedVisibilityAt m w 1).val) :
    StrictMono (fun k => (nestedVisibilityAt m w k).val) :=
  nestedVisibilityAt_strictMono_of_first_step_gain m w h

example (k : ℕ) (h : 0 < k) :
    (4/5 : ℝ) < (nestedVisibilityAt 4 fourFifthsVisibility k).val ∧
    (17/20 : ℝ) < elemFidelity (nestedVisibilityAt 4 fourFifthsVisibility k).val :=
  nestedRepeater_four_fifths_depth_four_sustains h

example (k : ℕ) : (nestedVisibilityAt 4 fourFifthsVisibility k).val < 1 :=
  nestedVisibilityAt_lt_one_of_gain 4 fourFifthsVisibility fourFifths_depth_four_gain k

example : nestedRawPairCount 4 1 = 32 ∧ nestedRawPairCount 4 2 = 1024 ∧
    segmentCount 2 = 4 := by
  norm_num [nestedRawPairCount, nestedBranchFactor, segmentCount]

example (m k : ℕ) : nestedRawPairCount m k = segmentCount k * 2^(m*k) :=
  nestedRawPairCount_per_segment m k
