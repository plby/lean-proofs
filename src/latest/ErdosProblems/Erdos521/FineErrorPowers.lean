/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Coarse summable bounds for the fine-grid error terms.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.FineGridPowers
import ErdosProblems.Erdos521.Decay

namespace Erdos521

open Filter

theorem fineGridLength_mul_rpow {j : ℕ} (hj : 0 < j) (p : ℝ) :
    (fineGridLength j : ℝ) * (j : ℝ) ^ p = (j : ℝ) ^ (18 + p) := by
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast hj
  rw [fineGridLength, Nat.cast_pow, ← Real.rpow_natCast (j : ℝ) 18, ← Real.rpow_add hj₀]
  norm_num

theorem fineGridThreshold_le_four {j : ℕ} (hj : 1 ≤ j) :
    fineGridThreshold j ≤ (j : ℝ) ^ (-4 : ℝ) := by
  rw [fineGridThreshold_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by norm_num)

theorem fine_grid_error_sum_bound {j : ℕ} (hj : 1 ≤ j) {B : ℝ} (hB : 0 ≤ B) :
    ((fineGridLength j : ℝ) + 1) * (B * fineGridThreshold j + 8 * (j : ℝ) ^ (-32 : ℝ)) ≤
      (2 * B + 16) * (j : ℝ) ^ (-4 : ℝ) := by
  have hj₀ : 0 < j := by omega
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hM : (1 : ℝ) ≤ fineGridLength j := by exact_mod_cast fineGridLength_pos hj₀
  have h₆ : (j : ℝ) ^ (-6 : ℝ) ≤ (j : ℝ) ^ (-4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hj' (by norm_num)
  have h₁₄ : (j : ℝ) ^ (-14 : ℝ) ≤ (j : ℝ) ^ (-4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hj' (by norm_num)
  have heq : (fineGridLength j : ℝ) * (j : ℝ) ^ (-32 : ℝ) = (j : ℝ) ^ (-14 : ℝ) := by
    convert fineGridLength_mul_rpow hj₀ (-32) using 1
    norm_num
  calc
    _ ≤ (2 * (fineGridLength j : ℝ)) * (B * fineGridThreshold j + 8 * (j : ℝ) ^ (-32 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by have := fineGridThreshold_pos hj₀; positivity)
    _ = 2 * B * ((fineGridLength j : ℝ) * fineGridThreshold j) +
        16 * ((fineGridLength j : ℝ) * (j : ℝ) ^ (-32 : ℝ)) := by ring
    _ = 2 * B * (j : ℝ) ^ (-6 : ℝ) + 16 * (j : ℝ) ^ (-14 : ℝ) := by
      rw [fineGrid_length_mul_threshold hj₀, heq]
    _ ≤ 2 * B * (j : ℝ) ^ (-4 : ℝ) + 16 * (j : ℝ) ^ (-4 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left h₆ (by positivity)) (mul_le_mul_of_nonneg_left h₁₄ (by norm_num))
    _ = _ := by ring

theorem eventually_dyadic_inverse_le_four :
    ∀ᶠ j : ℕ in atTop, (((2 ^ j : ℕ) : ℝ)) ^ (-1 : ℝ) ≤ (j : ℝ) ^ (-4 : ℝ) := by
  filter_upwards [eventually_exp_neg_rpow_le_rpow (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (by norm_num : (0 : ℝ) < 1) (-4)] with j hj
  rw [Real.rpow_one] at hj
  have heq : (((2 ^ j : ℕ) : ℝ)) ^ (-1 : ℝ) = Real.exp (-Real.log 2 * (j : ℝ)) := by
    rw [Real.rpow_neg_one, Nat.cast_pow, Nat.cast_ofNat,
      show -Real.log 2 * (j : ℝ) = -((j : ℝ) * Real.log 2) by ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [heq]
  exact hj

end Erdos521
