import Arxiv.Arxiv2411_18291.SmallRelativeRatio

/-!
# Edge drift with small relative errors

The actual count denominator is at least 63/64 of its main term. Keeping
this factor, and the quadratic error at most one eighth of the critical
scale, leaves a strict margin below the logarithmic comparison slope.
The lower comparison includes its survival correction.
-/

namespace Arxiv2411_18291

theorem edge_upper_numerator_small_error {κ x m u w C : ℝ}
    (hκ : 0 ≤ κ) (hx : 0 ≤ x) (hm : 0 ≤ m) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hC : 0 ≤ C) (hCw : C ≤ w / 100) (hum : u ≤ m / 8)
    (hu2 : u ^ 2 ≤ w * m / 8) (hxlo : m + u - w ≤ x) (hxhi : x ≤ m + u) :
    |x * (κ * (m - u) - C) - κ * m ^ 2| ≤
      (9 * κ / 8 + 9 / 800) * w * m := by
  have hmu : 0 ≤ m - u := by linarith only [hum, hm]
  have hlo := mul_le_mul_of_nonneg_right hxlo (mul_nonneg hκ hmu)
  have hhi := mul_le_mul_of_nonneg_right hxhi (mul_nonneg hκ hmu)
  have hxC := mul_le_mul_of_nonneg_right hxhi hC
  have hCm := mul_le_mul hCw (show m + u ≤ 9 * m / 8 by linarith only [hum])
    (add_nonneg hm hu) (by positivity : 0 ≤ w / 100)
  have hu2' := mul_le_mul_of_nonneg_left hu2 hκ
  have hwu := mul_nonneg (mul_nonneg hκ hw) hu
  have hCx := mul_nonneg hx hC
  have hκu := mul_nonneg hκ (sq_nonneg u)
  have hE : 0 ≤ (9 * κ / 8 + 9 / 800) * w * m := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo, hhi, hxC, hCm, hu2', hwu, hCx, hκu, hE]

theorem edge_lower_numerator_small_error {κ x m u w : ℝ}
    (hκ : 0 ≤ κ) (hm : 0 ≤ m) (hu : 0 ≤ u) (hw : 0 ≤ w) (hum : u ≤ m / 8)
    (hu2 : u ^ 2 ≤ w * m / 8) (hxlo : m - u ≤ x) (hxhi : x ≤ m - u + w) :
    |x * κ * (m + u) - κ * m ^ 2| ≤ 9 * κ / 8 * w * m := by
  have hfactor : 0 ≤ κ * (m + u) := mul_nonneg hκ (add_nonneg hm hu)
  have hlo := mul_le_mul_of_nonneg_right hxlo hfactor
  have hhi := mul_le_mul_of_nonneg_right hxhi hfactor
  have hmu := mul_le_mul_of_nonneg_left
    (show m + u ≤ 9 * m / 8 by linarith only [hum]) (mul_nonneg hκ hw)
  have hu2' := mul_le_mul_of_nonneg_left hu2 hκ
  have hκu := mul_nonneg hκ (sq_nonneg u)
  have hwm := mul_nonneg (mul_nonneg hκ hw) hm
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo, hhi, hmu, hu2', hκu, hwm]

theorem edge_ratio_small_error {N κ m w h h₀ v A : ℝ}
    (hκ : 0 ≤ κ) (hm : 0 ≤ m) (hh₀ : 0 < h₀)
    (hN : |N - κ * m ^ 2| ≤ A * w * m) (hd : |h - h₀| ≤ v)
    (hv : v ≤ h₀ / 64) (hvm : v * m ≤ 5 / 2 * w * h₀) :
    |N / h - κ * m ^ 2 / h₀| ≤ 64 / 63 * (A + 5 * κ / 2) * w * m / h₀ := by
  have hlo := (abs_le.mp hd).1
  have hh : 0 < h := by linarith only [hlo, hv, hh₀]
  have hB : h₀ ≤ 64 / 63 * h := by linarith only [hlo, hv]
  have hr := ratio_error_of_denominator_factor (mul_nonneg hκ (sq_nonneg m))
    hh hh₀ hN hd hB
  have hd' := mul_le_mul_of_nonneg_left hvm
    (show 0 ≤ (64 / 63 : ℝ) * κ * m / h₀ ^ 2 by positivity)
  have heq : (64 / 63 : ℝ) * κ * m / h₀ ^ 2 * (5 / 2 * w * h₀) =
      64 / 63 * (5 * κ / 2) * w * m / h₀ := by field_simp
  rw [heq] at hd'
  calc
    _ ≤ 64 / 63 * (A * w * m) / h₀ + 64 / 63 * (κ * m ^ 2) * v / h₀ ^ 2 := hr
    _ ≤ 64 / 63 * (A * w * m) / h₀ +
        64 / 63 * (5 * κ / 2) * w * m / h₀ := by
      apply add_le_add le_rfl
      convert hd' using 1
      ring
    _ = _ := by ring

theorem frozen_edge_upper_drift_of_small_error {κ x m u w C h h₀ v δ : ℝ}
    (hκ : 0 ≤ κ) (hκ4 : κ ≤ 4) (hx : 0 ≤ x) (hm : 0 ≤ m)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hC : 0 ≤ C) (hCw : C ≤ w / 100)
    (hum : u ≤ m / 8) (hu2 : u ^ 2 ≤ w * m / 8)
    (hxlo : m + u - w ≤ x) (hxhi : x ≤ m + u) (hh₀ : 0 < h₀)
    (hd : |h - h₀| ≤ v) (hv : v ≤ h₀ / 64) (hvm : v * m ≤ 5 / 2 * w * h₀)
    (hδ : δ ≤ 0)
    (hstep : -(κ * m ^ 2 / h₀) + (3 * κ + 23 / 8) * w * m / h₀ ≤ δ) :
    -(x / h * (κ * (m - u) - C)) - (1 - x / h) * δ ≤ 0 := by
  have hnum := edge_upper_numerator_small_error hκ hx hm hu hw hC hCw hum hu2 hxlo hxhi
  have hr := edge_ratio_small_error hκ hm hh₀ hnum hd hv hvm
  have hc : (64 / 63 : ℝ) * (9 * κ / 8 + 9 / 800 + 5 * κ / 2) ≤
      3 * κ + 23 / 8 := by linarith only [hκ4]
  have hr' : |x * (κ * (m - u) - C) / h - κ * m ^ 2 / h₀| ≤
      (3 * κ + 23 / 8) * w * m / h₀ := by
    apply hr.trans
    simpa only [mul_div_assoc, mul_assoc] using
      mul_le_mul_of_nonneg_right hc (show 0 ≤ w * (m / h₀) by positivity)
  have hlo := (abs_le.mp hd).1
  have hh : 0 < h := by linarith only [hlo, hv, hh₀]
  have hs := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hx hh.le) hδ
  have hrlo := (abs_le.mp hr').1
  rw [show x / h * (κ * (m - u) - C) = x * (κ * (m - u) - C) / h by ring]
  nlinarith only [hrlo, hstep, hs]

theorem frozen_edge_lower_drift_of_small_error {κ x m u w h h₀ v δ B : ℝ}
    (hκ : 0 ≤ κ) (hκ4 : κ ≤ 4) (hm : 0 ≤ m) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hwu : w ≤ u) (hum : u ≤ m / 8) (hu2 : u ^ 2 ≤ w * m / 8)
    (hxlo : m - u ≤ x) (hxhi : x ≤ m - u + w) (hh₀ : 0 < h₀)
    (hd : |h - h₀| ≤ v) (hv : v ≤ h₀ / 64) (hvm : v * m ≤ 5 / 2 * w * h₀)
    (hB : 0 ≤ B) (hBw : B ≤ w / 100) (hδB : -δ ≤ B)
    (hstep : δ ≤ -(κ * m ^ 2 / h₀) - (3 * κ + 23 / 8) * w * m / h₀) :
    0 ≤ -(x * κ * (m + u) / h) - (1 - x / h) * δ := by
  have hnum := edge_lower_numerator_small_error hκ hm hu hw hum hu2 hxlo hxhi
  have hr := edge_ratio_small_error hκ hm hh₀ hnum hd hv hvm
  have hlo := (abs_le.mp hd).1
  have hh : 0 < h := by linarith only [hlo, hv, hh₀]
  have hden : h₀ ≤ 64 / 63 * h := by linarith only [hlo, hv]
  have hx : 0 ≤ x := by linarith only [hxlo, hum, hm]
  have hxm : x ≤ m := by linarith only [hxhi, hwu]
  have hratio : x / h ≤ 64 / 63 * m / h₀ := by
    apply (div_le_div_of_nonneg_right hxm hh.le).trans
    apply (div_le_div_iff₀ hh hh₀).mpr
    have hh' := mul_le_mul_of_nonneg_right hden hm
    nlinarith only [hh']
  have hs : x / h * (-δ) ≤ (64 / 6300 : ℝ) * w * m / h₀ := by
    calc
      _ ≤ x / h * B := mul_le_mul_of_nonneg_left hδB (div_nonneg hx hh.le)
      _ ≤ (64 / 63 * m / h₀) * (w / 100) :=
        mul_le_mul hratio hBw hB (by positivity)
      _ = _ := by ring
  have hc : (64 / 63 : ℝ) * (9 * κ / 8 + 5 * κ / 2) + 64 / 6300 ≤
      3 * κ + 23 / 8 := by linarith only [hκ4]
  have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ w * (m / h₀) by positivity)
  have hrhi := (abs_le.mp hr).2
  simp only [div_eq_mul_inv] at hrhi hs hc' hstep ⊢
  nlinarith only [hrhi, hs, hc', hstep]

end Arxiv2411_18291
