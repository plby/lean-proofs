/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The exponential coefficient-window scale dominates every fixed polynomial in the dyadic index.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WindowScales

namespace Erdos521

open Filter

theorem two_pow_windowWidth_tendsto_atTop :
    Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ windowWidthScale j) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp windowWidthScale_tendsto_atTop

theorem eventually_const_mul_rpow_le_window_scale (C p : ℝ) :
    ∀ᶠ j : ℕ in atTop, C * (j : ℝ) ^ p ≤ (2 : ℝ) ^ windowWidthScale j := by
  filter_upwards [eventually_two_pow_neg_windowWidth_le (-(p + 1)),
    eventually_const_mul_rpow_le_rpow C (by linarith : p < p + 1), eventually_ge_atTop 1]
    with j hj hC hj₁
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hinv : ((2 : ℝ) ^ windowWidthScale j)⁻¹ ≤ ((j : ℝ) ^ (p + 1))⁻¹ := by
    simpa only [Real.rpow_neg hj₀.le] using hj
  exact hC.trans ((inv_le_inv₀ (by positivity) (Real.rpow_pos_of_pos hj₀ _)).mp hinv)

end Erdos521
