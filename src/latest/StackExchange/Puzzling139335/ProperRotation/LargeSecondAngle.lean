import Mathlib

namespace Puzzling139335.ProperRotation

private theorem second_circle_chord_bound {d q : ℝ}
    (hd : 0 < d) (hd_le_half : d ≤ 1 / 2) (hq : 0 < q)
    (hdq : d ^ 2 + q ^ 2 = 1) : 1 ≤ q + d / 3 := by
  have hd_square : d ^ 2 ≤ d / 2 := by
    nlinarith only [mul_nonneg hd.le (sub_nonneg.mpr hd_le_half)]
  have hq_le_one : q ≤ 1 := by
    nlinarith only [hdq, sq_nonneg d, sq_nonneg (q - 1)]
  have hq_ge_half : (1 : ℝ) / 2 ≤ q := by
    by_contra! hq_lt_half
    have hprod : 0 ≤ q * (1 / 2 - q) :=
      mul_nonneg hq.le (sub_nonneg.mpr hq_lt_half.le)
    nlinarith only [hdq, hd_square, hd_le_half, hprod, hq_lt_half]
  have hprod : 0 ≤ (1 - q) * (q - 1 / 2) :=
    mul_nonneg (sub_nonneg.mpr hq_le_one) (sub_nonneg.mpr hq_ge_half)
  nlinarith only [hdq, hd_square, hprod]

/-- The first intersection numerator is positive when the second cosine is at most one half.
The proof uses only the source strip and face-center inequalities, not the center-preimage
constraints or an assumption on the sum of the two angles. -/
theorem ns_pos_of_second_cos_le_half {c s d q a u v w z X Y : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hs_lt_one : s < 1)
    (hd : 0 < d) (hd_le_half : d ≤ 1 / 2) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (hX : X = -c * u - s * v) (hY : Y = s * u - c * v)
    (hX_nonneg : 0 ≤ X) (hY_nonneg : 0 ≤ Y) (hY_le_half : Y ≤ 1 / 2)
    (hz : z ≤ 1 / 2 - q) (hza : d * a - z ≤ 1 / 2)
    (hface : q * w + d * z + d * (1 / 2 - a) ≤ 1 / 2) :
    0 < q * (1 - u - w) - d * (v + z) := by
  have hbase : 2 * q + d / 2 - 3 / 2 ≤ q * (1 - w) - d * z := by
    nlinarith only [hz, hza, hface]
  have hS : 0 < s * d + c * q :=
    add_pos (mul_pos hs hd) (mul_pos hc hq)
  have hcenter : -(s * q) / 2 ≤ (s * d + c * q) * X + (c * d - s * q) * Y := by
    have hSX := mul_nonneg hS.le hX_nonneg
    have hcdY := mul_nonneg (mul_nonneg hc.le hd.le) hY_nonneg
    have hsqY := mul_nonneg (mul_nonneg hs.le hq.le) (sub_nonneg.mpr hY_le_half)
    nlinarith only [hSX, hcdY, hsqY]
  have hid : q * (1 - u - w) - d * (v + z) =
      q * (1 - w) - d * z + (s * d + c * q) * X + (c * d - s * q) * Y := by
    rw [hX, hY]
    linear_combination (q * u + d * v) * hcs
  have hangle := second_circle_chord_bound hd hd_le_half hq hdq
  have hgap : 0 < (1 - s) * q := mul_pos (sub_pos.mpr hs_lt_one) hq
  nlinarith only [hbase, hcenter, hid, hangle, hgap]

end Puzzling139335.ProperRotation
