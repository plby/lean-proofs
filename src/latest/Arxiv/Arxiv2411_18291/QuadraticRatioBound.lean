import Arxiv.Arxiv2411_18291.EdgeNumeratorBounds

/-! # Ratio control for a quadratic drift main term -/

namespace Arxiv2411_18291

theorem ratio_error_from_quadratic_main_term {N κ m h h₀ A t v : ℝ}
    (hκ : 0 ≤ κ) (hm : 0 ≤ m) (hh₀ : 0 < h₀)
    (hN : |N - κ * m ^ 2| ≤ A * t * m) (hd : |h - h₀| ≤ v)
    (hv : v ≤ h₀ / 2) (hvm : v * m ≤ t * h₀) :
    |N / h - κ * m ^ 2 / h₀| ≤ (2 * A + 2 * κ) * t * m / h₀ := by
  have h := ratio_error_of_half_bound (mul_nonneg hκ (sq_nonneg m)) hh₀ hN hd hv
  have hden : 2 * (κ * m ^ 2) * v / h₀ ^ 2 ≤ 2 * κ * t * m / h₀ := by
    calc
      _ = (2 * κ * m / h₀ ^ 2) * (v * m) := by ring
      _ ≤ (2 * κ * m / h₀ ^ 2) * (t * h₀) :=
        mul_le_mul_of_nonneg_left hvm (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ 2 * (A * t * m) / h₀ + 2 * (κ * m ^ 2) * v / h₀ ^ 2 := h
    _ ≤ 2 * (A * t * m) / h₀ + 2 * κ * t * m / h₀ := add_le_add le_rfl hden
    _ = _ := by ring

end Arxiv2411_18291
