import Mathlib

/-!
# Scalar bounds for naturally ordered straddling support normals

The height constraints force both positive cosines below one half. Together with the unit
circle identities this bounds the tangent-direction dot product below by one half. The
width constraint is also expressed in a form with no division.
-/

namespace Puzzling139335.TwoSideFaces

/-- A positive point of the unit circle has both coordinates strictly below one. -/
theorem positive_circle_lt_one {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hcs : c ^ 2 + s ^ 2 = 1) : c < 1 ∧ s < 1 := by
  constructor
  · nlinarith only [hcs, sq_nonneg (c - 1), mul_pos hs hs]
  · nlinarith only [hcs, sq_nonneg (s - 1), mul_pos hc hc]

/-- A face of length `1 - 2*b` fitting above height `b` forces its cosine below one half. -/
theorem cos_le_half_of_height {b c : ℝ} (hb_lt_half : b < 1 / 2)
    (hheight : b + (1 - 2 * b) * c ≤ 1 / 2) : c ≤ 1 / 2 := by
  have hfactor : 0 < 1 - 2 * b := by linarith only [hb_lt_half]
  have hmul : (1 - 2 * b) * c ≤ (1 - 2 * b) * (1 / 2) := by
    nlinarith only [hheight]
  exact le_of_mul_le_mul_left hmul hfactor

/-- Tangent width at most one implies the rationalized bound `a*(1+s) ≤ c`. -/
theorem tangent_width_bound {c s a : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hcs : c ^ 2 + s ^ 2 = 1) (hwidth : s + a * c ≤ 1) :
    a * (1 + s) ≤ c := by
  have hfactor : 0 ≤ 1 + s := by linarith only [hs]
  have hwidth_mul := mul_le_mul_of_nonneg_right hwidth hfactor
  have hmul : c * (a * (1 + s)) ≤ c * c := by
    nlinarith only [hwidth_mul, hcs]
  exact le_of_mul_le_mul_left hmul hc

/-- When both positive cosines are at most one half, the tangent-direction dot product
`s*q - c*d` is at least one half. The argument is polynomial and uses no square roots. -/
theorem circle_dot_ge_half {c s d q : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (hc_half : c ≤ 1 / 2) (hd_half : d ≤ 1 / 2) :
    (1 : ℝ) / 2 ≤ s * q - c * d := by
  have hc_sq : c ^ 2 ≤ 1 / 4 := by
    nlinarith only [hc_half, mul_nonneg hc.le (sub_nonneg.mpr hc_half)]
  have hd_sq : d ^ 2 ≤ 1 / 4 := by
    nlinarith only [hd_half, mul_nonneg hd.le (sub_nonneg.mpr hd_half)]
  have hs_sq : (3 : ℝ) / 4 ≤ s ^ 2 := by linarith only [hcs, hc_sq]
  have hq_sq : (3 : ℝ) / 4 ≤ q ^ 2 := by linarith only [hdq, hd_sq]
  have hsq : (3 : ℝ) / 4 ≤ s * q := by
    rcases le_total s q with hle | hle
    · nlinarith only [hs_sq, mul_le_mul_of_nonneg_left hle hs.le]
    · nlinarith only [hq_sq, mul_le_mul_of_nonneg_left hle hq.le]
  have hcd : c * d ≤ (1 / 2 : ℝ) * (1 / 2) :=
    mul_le_mul hc_half hd_half hd.le (by norm_num)
  linarith only [hsq, hcd]

end Puzzling139335.TwoSideFaces
