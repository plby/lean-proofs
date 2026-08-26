/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Power identities for the fine-grid threshold and error estimates.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.DyadicFineGrid

namespace Erdos521

theorem fineGridThreshold_eq_rpow (j : ℕ) : fineGridThreshold j = (j : ℝ) ^ (-24 : ℝ) := by
  rw [Real.rpow_neg (Nat.cast_nonneg j), Real.rpow_ofNat]
  rfl

theorem fineGridRelativeWidth_eq_rpow (j : ℕ) : fineGridRelativeWidth j = (j : ℝ) ^ (-18 : ℝ) := by
  rw [Real.rpow_neg (Nat.cast_nonneg j), Real.rpow_ofNat]
  rfl

theorem fineGrid_threshold_variance_lower {j : ℕ} (hj : 0 < j) {V : ℝ}
    (hV : 2 * (j : ℝ) ^ 50 ≤ V) : (j : ℝ) ^ 2 ≤ (fineGridThreshold j ^ 2 / 2) * V := by
  have hj₀ : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  calc
    (j : ℝ) ^ 2 = (fineGridThreshold j ^ 2 / 2) * (2 * (j : ℝ) ^ 50) := by
      unfold fineGridThreshold
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hV (by positivity)

theorem fineGrid_length_mul_threshold {j : ℕ} (hj : 0 < j) :
    (fineGridLength j : ℝ) * fineGridThreshold j = (j : ℝ) ^ (-6 : ℝ) := by
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast hj
  rw [fineGridLength, Nat.cast_pow, fineGridThreshold_eq_rpow,
    ← Real.rpow_natCast (j : ℝ) 18, ← Real.rpow_add hj₀]
  norm_num

theorem fineGrid_truncation_power {j : ℕ} (hj : 0 < j) :
    (j : ℝ) ^ (-80 : ℝ) / fineGridThreshold j ^ 2 = (j : ℝ) ^ (-32 : ℝ) := by
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast hj
  rw [fineGridThreshold_eq_rpow, ← Real.rpow_mul_natCast hj₀.le,
    ← Real.rpow_sub hj₀]
  norm_num

end Erdos521
