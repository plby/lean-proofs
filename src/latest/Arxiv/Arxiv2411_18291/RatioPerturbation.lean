import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Explicit errors when a positive denominator is perturbed -/

namespace Arxiv2411_18291

theorem reciprocal_error_of_half_bound {h h₀ v : ℝ} (hh₀ : 0 < h₀)
    (hd : |h - h₀| ≤ v) (hv : v ≤ h₀ / 2) :
    |1 / h - 1 / h₀| ≤ 2 * v / h₀ ^ 2 := by
  have hv0 : 0 ≤ v := (abs_nonneg _).trans hd
  have hlo := (abs_le.mp hd).1
  have hh : 0 < h := by linarith
  have hhalf : h₀ ≤ 2 * h := by linarith
  have heq : 1 / h - 1 / h₀ = (h₀ - h) / (h * h₀) := by field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hh hh₀)]
  calc
    _ ≤ v / (h * h₀) :=
      div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hd) (by positivity)
    _ ≤ _ := by
      apply (div_le_div_iff₀ (mul_pos hh hh₀) (pow_pos hh₀ 2)).mpr
      have hmul := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hv0 hh₀.le)
      nlinarith only [hmul]

theorem ratio_error_of_half_bound {N N₀ h h₀ E v : ℝ} (hN₀ : 0 ≤ N₀) (hh₀ : 0 < h₀)
    (hN : |N - N₀| ≤ E) (hd : |h - h₀| ≤ v) (hv : v ≤ h₀ / 2) :
    |N / h - N₀ / h₀| ≤ 2 * E / h₀ + 2 * N₀ * v / h₀ ^ 2 := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hN
  have hlo := (abs_le.mp hd).1
  have hh : 0 < h := by linarith
  have hhalf : h₀ ≤ 2 * h := by linarith
  have hEdiv : E / h ≤ 2 * E / h₀ := by
    apply (div_le_div_iff₀ hh hh₀).mpr
    have hmul := mul_le_mul_of_nonneg_left hhalf hE
    nlinarith only [hmul]
  calc
    _ = |(N - N₀) / h + N₀ * (1 / h - 1 / h₀)| := by congr 1; ring
    _ ≤ |(N - N₀) / h| + |N₀ * (1 / h - 1 / h₀)| := abs_add_le _ _
    _ = |N - N₀| / h + N₀ * |1 / h - 1 / h₀| := by
      rw [abs_div, abs_of_pos hh, abs_mul, abs_of_nonneg hN₀]
    _ ≤ E / h + N₀ * (2 * v / h₀ ^ 2) :=
      add_le_add (div_le_div_of_nonneg_right hN hh.le)
        (mul_le_mul_of_nonneg_left (reciprocal_error_of_half_bound hh₀ hd hv) hN₀)
    _ ≤ 2 * E / h₀ + N₀ * (2 * v / h₀ ^ 2) := add_le_add hEdiv le_rfl
    _ = _ := by ring

end Arxiv2411_18291
