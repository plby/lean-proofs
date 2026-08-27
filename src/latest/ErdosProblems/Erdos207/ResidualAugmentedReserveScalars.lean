/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualAdjoinScalars

/-! # Density and constant budgets for the augmented-reserve partition -/

namespace Erdos207

open scoped NNReal

theorem residualAugmentedReserveAdjoinPartitionTerm_le
    (p alpha eta C factor b nInv oldScale newScale r r' : ℝ≥0)
    (a s e t d l u f : ℕ) (hcard : d = s + t) (hRcard : f = l + u)
    (hC : 1 ≤ C) (hfactor : 1 ≤ factor) (halpha : alpha ≤ 1) (heta : eta ≤ 1)
    (hr : r ≤ r') (hetar : eta ≤ r')
    (hscale : oldScale * (alpha * p ^ 3) ^ t ≤ factor ^ t * newScale) :
    (alpha ^ t * eta ^ u) * (C ^ (a + s + (3 * t + e) + l) *
      (p ^ (3 * t + e) * r ^ l * nInv ^ a * oldScale + b)) ≤
      (C ^ 3 * factor) ^ (a + d + e + f) *
        (p ^ e * r' ^ f * nInv ^ a * newScale + b) := by
  have hreserve : eta ^ u * r ^ l ≤ r' ^ f := by
    calc
      _ ≤ r' ^ u * r' ^ l := mul_le_mul (pow_le_pow_left' hetar u) (pow_le_pow_left' hr l) zero_le zero_le
      _ = _ := by rw [hRcard, pow_add]; ring
  have hexp : C ^ (a + s + (3 * t + e) + l) ≤ C ^ (a + s + (3 * t + e) + f) :=
    pow_le_pow_right₀ hC (by omega)
  have hbound : eta ^ u * (C ^ (a + s + (3 * t + e) + l) *
      (p ^ (3 * t + e) * r ^ l * nInv ^ a * oldScale + b)) ≤
      C ^ (a + s + (3 * t + e) + f) *
        (p ^ (3 * t + e) * r' ^ f * nInv ^ a * oldScale + b) := by
    calc
      _ = C ^ (a + s + (3 * t + e) + l) *
          ((p ^ (3 * t + e) * nInv ^ a * oldScale) * (eta ^ u * r ^ l) + eta ^ u * b) := by ring
      _ ≤ C ^ (a + s + (3 * t + e) + f) *
          ((p ^ (3 * t + e) * nInv ^ a * oldScale) * r' ^ f + b) :=
        mul_le_mul hexp (add_le_add (mul_le_mul_of_nonneg_left hreserve zero_le)
          (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le heta))) zero_le zero_le
      _ = _ := by ring
  calc
    _ = alpha ^ t * (eta ^ u * (C ^ (a + s + (3 * t + e) + l) *
        (p ^ (3 * t + e) * r ^ l * nInv ^ a * oldScale + b))) := by ring
    _ ≤ alpha ^ t * (C ^ (a + s + (3 * t + e) + f) *
        (p ^ (3 * t + e) * r' ^ f * nInv ^ a * oldScale + b)) :=
      mul_le_mul_of_nonneg_left hbound zero_le
    _ ≤ _ := residualReserveAdjoinPartitionTerm_le p alpha C factor b nInv oldScale newScale r'
      a s e t d f hcard hC hfactor halpha hscale

end Erdos207
