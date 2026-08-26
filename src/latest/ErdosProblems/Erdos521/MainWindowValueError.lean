/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform quantitative truncation errors at the fine-grid value threshold.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainWindowGeometry
import ErdosProblems.Erdos521.DyadicWindowError
import ErdosProblems.Erdos521.FineGridPowers
import ErdosProblems.Erdos521.MainBinVariance

namespace Erdos521

open MeasureTheory Filter

theorem eventually_mainBin_window_value_error :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)),
      sequenceLaw.real {ε | fineGridThreshold j * Real.sqrt (geometricVariance x (2 ^ j + 1)) ≤
        |powerSum ε (2 ^ j + 1) x - windowPowerSum ε (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j)) x|} ≤
        8 * (j : ℝ) ^ (-32 : ℝ) := by
  filter_upwards [eventually_mainBin_point_variance, eventually_two_pow_neg_windowWidth_le (-80),
    eventually_ge_atTop 1] with j hj hscale hj₁
  intro k hk x hx
  have hj₀ : 0 < j := by omega
  have hp := hj k hk x hx
  have h := dyadic_window_normalized_error_probability (2 ^ j) k (windowWidthScale j)
    (main_window_exponents hk).1 (main_window_upper hk) (by linarith [hp.1] : 0 ≤ x) hx
    (fineGridThreshold_pos hj₀) hp.2.2.1
  apply h.trans
  calc
    _ ≤ 8 * (j : ℝ) ^ (-80 : ℝ) / fineGridThreshold j ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by norm_num)) (sq_nonneg _)
    _ = _ := by rw [mul_div_assoc, fineGrid_truncation_power hj₀]

end Erdos521
