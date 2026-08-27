/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Variation of two signed perturbed profile values -/

namespace Erdos4b.FGKMT

theorem perturbed_profile_pair_bound {y z f g U A ε D : ℝ}
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hf : 0 ≤ f) (hfU : f ≤ U)
    (hy : |y - A * f| ≤ ε * A * U) (hz : |z - A * g| ≤ ε * A * U)
    (hvar : |g - f| ≤ D * U) :
    |y * (z - y)| ≤ 2 * A ^ 2 * U ^ 2 * (D + 2 * ε) := by
  have hyabs : |y| ≤ 2 * A * U := by
    calc
      _ = |(y - A * f) + A * f| := by congr 1; ring
      _ ≤ |y - A * f| + |A * f| := abs_add_le _ _
      _ = |y - A * f| + A * f := by rw [abs_of_nonneg (mul_nonneg hA hf)]
      _ ≤ ε * A * U + A * U := add_le_add hy (mul_le_mul_of_nonneg_left hfU hA)
      _ ≤ _ := by nlinarith [mul_nonneg hA hU]
  have hyz : |z - y| ≤ A * U * (D + 2 * ε) := by
    calc
      _ = |((z - A * g) + A * (g - f)) + (A * f - y)| := by congr 1; ring
      _ ≤ (|z - A * g| + |A * (g - f)|) + |A * f - y| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = (|z - A * g| + A * |g - f|) + |y - A * f| := by
        rw [abs_mul, abs_of_nonneg hA, abs_sub_comm (A * f) y]
      _ ≤ (ε * A * U + A * (D * U)) + ε * A * U :=
        add_le_add (add_le_add hz (mul_le_mul_of_nonneg_left hvar hA)) hy
      _ = _ := by ring
  rw [abs_mul]
  calc
    _ ≤ (2 * A * U) * (A * U * (D + 2 * ε)) :=
      mul_le_mul hyabs hyz (abs_nonneg _) (by positivity)
    _ = _ := by ring

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.perturbed_profile_pair_bound
