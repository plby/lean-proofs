/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Power identities for balancing the grid probability and moment errors.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

theorem refinement_probability_power {x D : ℝ} (hx : 0 < x) (hD : 0 ≤ D) (C : ℝ) :
    x ^ (1 / 6 : ℝ) * x * C * (D / x) ^ (4 / 3 : ℝ) =
      C * D ^ (4 / 3 : ℝ) * x ^ (-(1 / 6 : ℝ)) := by
  have hprod : x ^ (1 / 6 : ℝ) * x = x ^ (7 / 6 : ℝ) := by
    calc
      x ^ (1 / 6 : ℝ) * x = x ^ (1 / 6 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((1 / 6 : ℝ) + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by norm_num
  calc
    x ^ (1 / 6 : ℝ) * x * C * (D / x) ^ (4 / 3 : ℝ) =
        C * D ^ (4 / 3 : ℝ) * ((x ^ (1 / 6 : ℝ) * x) / x ^ (4 / 3 : ℝ)) := by
      rw [Real.div_rpow hD hx.le]
      ring
    _ = _ := by
      rw [hprod, ← Real.rpow_sub hx]
      norm_num

theorem refinement_moment_power {x : ℝ} (hx : 0 ≤ x) (B : ℝ) :
    B / (x ^ (1 / 6 : ℝ)) ^ 7 = B * x ^ (-(7 / 6 : ℝ)) := by
  rw [← Real.rpow_mul_natCast hx, div_eq_mul_inv, ← Real.rpow_neg hx]
  norm_num

end Erdos521
