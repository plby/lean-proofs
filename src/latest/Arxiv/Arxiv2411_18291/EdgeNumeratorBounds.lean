import Arxiv.Arxiv2411_18291.RatioPerturbation

/-!
# Cancellation in the edge-degree drift near an error boundary

The leading terms cancel the first-order regularity error. Only the
critical-window width, the square of that error, and the codegree error
remain. Both upper and lower critical intervals are treated explicitly.
-/

namespace Arxiv2411_18291

theorem edge_upper_numerator_error {κ x m u w t C : ℝ}
    (hκ : 0 ≤ κ) (hx : 0 ≤ x) (hm : 0 ≤ m) (hu : 0 ≤ u)
    (ht : 0 ≤ t) (hC : 0 ≤ C) (hCt : C ≤ t) (hwt : w ≤ t) (hum : u ≤ m)
    (hu2 : u ^ 2 ≤ t * m) (hxlo : m + u - w ≤ x) (hxhi : x ≤ m + u) :
    |x * (κ * (m - u) - C) - κ * m ^ 2| ≤ (2 * κ + 2) * t * m := by
  have hlo := mul_le_mul_of_nonneg_right hxlo (mul_nonneg hκ hm)
  have hxu := mul_le_mul_of_nonneg_right hxhi (mul_nonneg hκ hu)
  have hx2 : x ≤ 2 * m := by linarith only [hxhi, hum]
  have hcx := mul_le_mul hCt hx2 hx ht
  have hwm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwt hm) hκ
  have hu2' := mul_le_mul_of_nonneg_left hu2 hκ
  have hlow : κ * m ^ 2 - (2 * κ + 2) * t * m ≤ x * (κ * (m - u) - C) := by
    nlinarith only [hlo, hxu, hcx, hwm, hu2']
  have hbase := mul_le_mul_of_nonneg_right hxhi
    (mul_nonneg hκ (sub_nonneg.mpr hum))
  have hcx0 := mul_nonneg hC hx
  have hκu := mul_nonneg hκ (sq_nonneg u)
  have hhigh : x * (κ * (m - u) - C) ≤ κ * m ^ 2 := by
    nlinarith only [hbase, hcx0, hκu]
  have hb : 0 ≤ (2 * κ + 2) * t * m := by positivity
  exact abs_le.mpr ⟨by linarith only [hlow], by linarith only [hhigh, hb]⟩

theorem edge_lower_numerator_error {κ x m u w t : ℝ}
    (hκ : 0 ≤ κ) (hm : 0 ≤ m) (hu : 0 ≤ u) (ht : 0 ≤ t)
    (hwt : w ≤ t) (hum : u ≤ m) (hu2 : u ^ 2 ≤ t * m)
    (hxlo : m - u ≤ x) (hxhi : x ≤ m - u + w) :
    |x * κ * (m + u) - κ * m ^ 2| ≤ 2 * κ * t * m := by
  have hfactor : 0 ≤ κ * (m + u) := mul_nonneg hκ (add_nonneg hm hu)
  have hlo := mul_le_mul_of_nonneg_right hxlo hfactor
  have hhi := mul_le_mul_of_nonneg_right hxhi hfactor
  have hmu : m + u ≤ 2 * m := by linarith only [hum]
  have hwm := mul_le_mul hwt hmu (add_nonneg hm hu) ht
  have hwm' := mul_le_mul_of_nonneg_left hwm hκ
  have hu2' := mul_le_mul_of_nonneg_left hu2 hκ
  have hu20 := mul_nonneg hκ (sq_nonneg u)
  have htm := mul_nonneg hκ (mul_nonneg ht hm)
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo, hhi, hwm', hu2', hu20, htm]

end Arxiv2411_18291
