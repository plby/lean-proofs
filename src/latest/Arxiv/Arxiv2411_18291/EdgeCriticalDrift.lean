import Arxiv.Arxiv2411_18291.QuadraticRatioBound

/-!
# Numerical drift inequalities in the two edge critical intervals

These inequalities retain the survival factor of the frozen comparison.
The lower critical interval has an additional explicit allowance for this
factor; it is not discarded as in the upper-interval estimate.
-/

namespace Arxiv2411_18291

theorem frozen_edge_upper_drift_nonpos {κ x m u w t C h h₀ v δ : ℝ}
    (hκ : 0 ≤ κ) (hx : 0 ≤ x) (hm : 0 ≤ m) (hu : 0 ≤ u) (ht : 0 ≤ t)
    (hC : 0 ≤ C) (hCt : C ≤ t) (hwt : w ≤ t) (hum : u ≤ m) (hu2 : u ^ 2 ≤ t * m)
    (hxlo : m + u - w ≤ x) (hxhi : x ≤ m + u) (hh₀ : 0 < h₀)
    (hd : |h - h₀| ≤ v) (hv : v ≤ h₀ / 2) (hvm : v * m ≤ t * h₀)
    (hδ : δ ≤ 0) (hstep : -(κ * m ^ 2 / h₀) + (6 * κ + 4) * t * m / h₀ ≤ δ) :
    -(x / h * (κ * (m - u) - C)) - (1 - x / h) * δ ≤ 0 := by
  have hnum := edge_upper_numerator_error hκ hx hm hu ht hC hCt hwt hum hu2 hxlo hxhi
  have hr := ratio_error_from_quadratic_main_term hκ hm hh₀ hnum hd hv hvm
  rw [show 2 * (2 * κ + 2) + 2 * κ = 6 * κ + 4 by ring] at hr
  have hrlo := (abs_le.mp hr).1
  have hlo := (abs_le.mp hd).1
  have hh : 0 < h := by linarith only [hlo, hv, hh₀]
  have hsurvive := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hx hh.le) hδ
  have heq : x / h * (κ * (m - u) - C) = x * (κ * (m - u) - C) / h := by ring
  rw [heq]
  nlinarith only [hrlo, hstep, hsurvive]

theorem frozen_edge_lower_drift_nonneg {κ x m u w t h h₀ v δ B : ℝ}
    (hκ : 0 ≤ κ) (hm : 0 ≤ m) (hu : 0 ≤ u) (ht : 0 ≤ t) (hwt : w ≤ t)
    (htm : t ≤ m) (hum : u ≤ m) (hu2 : u ^ 2 ≤ t * m)
    (hxlo : m - u ≤ x) (hxhi : x ≤ m - u + w) (hh₀ : 0 < h₀)
    (hd : |h - h₀| ≤ v) (hv : v ≤ h₀ / 2) (hvm : v * m ≤ t * h₀)
    (hB : 0 ≤ B) (hδB : -δ ≤ B)
    (hstep : δ ≤ -(κ * m ^ 2 / h₀) - 6 * κ * t * m / h₀ - 4 * m * B / h₀) :
    0 ≤ -(x * κ * (m + u) / h) - (1 - x / h) * δ := by
  have hnum := edge_lower_numerator_error hκ hm hu ht hwt hum hu2 hxlo hxhi
  have hr := ratio_error_from_quadratic_main_term hκ hm hh₀ hnum hd hv hvm
  rw [show 2 * (2 * κ) + 2 * κ = 6 * κ by ring] at hr
  have hrhi := (abs_le.mp hr).2
  have hlo := (abs_le.mp hd).1
  have hh : 0 < h := by linarith only [hlo, hv, hh₀]
  have hhalf : h₀ ≤ 2 * h := by linarith only [hlo, hv]
  have hx : 0 ≤ x := by linarith only [hxlo, hum]
  have hx2 : x ≤ 2 * m := by linarith only [hxhi, hu, hwt, htm]
  have hratio : x / h ≤ 4 * m / h₀ := by
    apply (div_le_div_of_nonneg_right hx2 hh.le).trans
    apply (div_le_div_iff₀ hh hh₀).mpr
    have hmul := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2 * m by positivity)
    nlinarith only [hmul]
  have hsurvive : (x / h) * (-δ) ≤ 4 * m * B / h₀ := by
    calc
      _ ≤ (x / h) * B := mul_le_mul_of_nonneg_left hδB (div_nonneg hx hh.le)
      _ ≤ (4 * m / h₀) * B := mul_le_mul_of_nonneg_right hratio hB
      _ = _ := by ring
  nlinarith only [hrhi, hstep, hsurvive]

end Arxiv2411_18291
