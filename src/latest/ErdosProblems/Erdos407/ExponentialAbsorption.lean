/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A fixed exponential factor is absorbed by a larger exponential saving

This elementary real-analysis lemma isolates the last numerical step in the
GLR rank-drop contradiction.
-/

namespace Erdos407.ExponentialAbsorption

/-- If the logarithmic cost of a fixed base consumes at most one quarter of
the available saving, while the remaining factor has half-saving decay, then
their product is strictly less than one. -/
theorem rpow_mul_lt_one_of_log_cost
    {B t blocks D logQ₀ κ R : ℝ}
    (hB : 1 ≤ B)
    (hlogQ₀ : 0 < logQ₀)
    (hD : 0 < D) (hκ : 0 < κ)
    (ht : t ≤ blocks * D / logQ₀)
    (hcost : Real.log B * blocks / logQ₀ ≤ κ / 4)
    (hR : R ≤ Real.exp (-(κ * D / 2))) :
    B ^ t * R < 1 := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hdegreeCost : Real.log B * t ≤ κ * D / 4 := by
    calc
      Real.log B * t ≤ Real.log B * (blocks * D / logQ₀) :=
        mul_le_mul_of_nonneg_left ht hlogB
      _ = (Real.log B * blocks / logQ₀) * D := by
        field_simp
      _ ≤ (κ / 4) * D := mul_le_mul_of_nonneg_right hcost hD.le
      _ = κ * D / 4 := by ring
  have hpow : B ^ t = Real.exp (Real.log B * t) := by
    rw [Real.rpow_def_of_pos hBpos]
  calc
    B ^ t * R ≤ B ^ t * Real.exp (-(κ * D / 2)) :=
      mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hBpos.le _)
    _ = Real.exp (Real.log B * t - κ * D / 2) := by
      rw [hpow, ← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-(κ * D / 4)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hκ hD])

end Erdos407.ExponentialAbsorption
