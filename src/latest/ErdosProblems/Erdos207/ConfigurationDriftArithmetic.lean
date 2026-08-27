/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DriftErrorArithmetic

/-! # Explicit numerator and denominator errors in the coupled drift equations -/

namespace Erdos207

theorem configuration_numerator_error_le
    (u v y z α β H eu ev : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hu : |u - y| ≤ eu) (hv : |v - z| ≤ ev) :
    |(α * u - β * v * H) - (α * y - β * z * H)| ≤ α * eu + β * |H| * ev := by
  have hu' : |α * u - α * y| ≤ α * eu := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hα]
    exact mul_le_mul_of_nonneg_left hu hα
  have hv' : |β * v * H - β * z * H| ≤ β * |H| * ev := by
    have he : β * v * H - β * z * H = (β * H) * (v - z) := by ring
    rw [he, abs_mul, abs_mul, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left hv (mul_nonneg hβ (abs_nonneg H))
  exact abs_difference_error_le hu' hv'

theorem configuration_drift_quotient_error_le
    (μ u v y z α β H R A eta eu ev eA : ℝ)
    (hR : 0 < R) (hA : 0 < A) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hraw : |μ - (α * u - β * v * H) / R| ≤ eta)
    (hu : |u - y| ≤ eu) (hv : |v - z| ≤ ev) (hdenom : |R - A| ≤ eA) :
    |μ - (α * y - β * z * H) / A| ≤
      eta + (α * eu + β * |H| * ev) / R + |α * y - β * z * H| * eA / (R * A) := by
  have hnum := configuration_numerator_error_le u v y z α β H eu ev hα hβ hu hv
  have hquot := abs_div_sub_div_le_of_errors hR hA hnum hdenom
  calc
    _ ≤ |μ - (α * u - β * v * H) / R| +
        |(α * u - β * v * H) / R - (α * y - β * z * H) / A| := abs_sub_le _ _ _
    _ ≤ eta + ((α * eu + β * |H| * ev) / R + |α * y - β * z * H| * eA / (R * A)) :=
      add_le_add hraw hquot
    _ = _ := by ring

theorem pair_quadratic_numerator_error_le
    (u x H e : ℝ) (hu : |u - x| ≤ e) :
    |u * (H - u) - x * (H - x)| ≤ e * (|H| + |u| + |x|) := by
  have he : u * (H - u) - x * (H - x) = (u - x) * (H - u - x) := by ring
  have hsum : |H - u - x| ≤ |H| + |u| + |x| :=
    (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  rw [he, abs_mul]
  exact mul_le_mul hu hsum (abs_nonneg _) (le_trans (abs_nonneg _) hu)

end Erdos207
