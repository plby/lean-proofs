/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource

/-!
# Endpoint construction of the Bilu dyadic range window

All fields of `DyadicRangeWindow` are monotone across the closed range.
Consequently outer arithmetic only needs to check the upper fold at `high`
and every lower condition at `low`.
-/

namespace Erdos186.CFP.PreprocessingBilu

noncomputable section

/-- Construct the full dyadic range window from its two endpoint checks. -/
theorem DyadicRangeWindow.of_endpoints
    {n low high first horizonFactor D propernessDenominator : ℕ}
    (hoffset : Nat.clog 2 horizonFactor ≤ low)
    (hfoldHigh : 2 ^ high ≤ n)
    (hpowerLow : n ≤
      (horizonFactor *
        2 ^ (low - Nat.clog 2 horizonFactor)) ^ (D - 1))
    (hfirstLow : first < low - Nat.clog 2 horizonFactor)
    (hlastLow :
      (2 * D + 1) * first + 2 * horizonFactor * (D - 1) <
        low - Nat.clog 2 horizonFactor)
    (hindexLow : preprocessingIndexBound D propernessDenominator ≤
      2 ^ low) :
    DyadicRangeWindow n low high first horizonFactor D
      propernessDenominator where
  offset_le_low := hoffset
  fold_le_n := by
    intro level hlow hhigh
    exact (Nat.pow_le_pow_right (by omega : 0 < 2) hhigh).trans hfoldHigh
  n_le_horizon_pow := by
    intro level hlow _hhigh
    have hsub : low - Nat.clog 2 horizonFactor ≤
        level - Nat.clog 2 horizonFactor :=
      Nat.sub_le_sub_right hlow _
    have hpow : 2 ^ (low - Nat.clog 2 horizonFactor) ≤
        2 ^ (level - Nat.clog 2 horizonFactor) :=
      Nat.pow_le_pow_right (by omega) hsub
    exact hpowerLow.trans (Nat.pow_le_pow_left
      (Nat.mul_le_mul_left horizonFactor hpow) _)
  first_lt_last := by
    intro level hlow _hhigh
    exact hfirstLow.trans_le (Nat.sub_le_sub_right hlow _)
  last_large := by
    intro level hlow _hhigh
    exact hlastLow.trans_le (Nat.sub_le_sub_right hlow _)
  index_le_fold := by
    intro level hlow _hhigh
    exact hindexLow.trans (Nat.pow_le_pow_right (by omega) hlow)

end

end Erdos186.CFP.PreprocessingBilu

#print axioms
  Erdos186.CFP.PreprocessingBilu.DyadicRangeWindow.of_endpoints
