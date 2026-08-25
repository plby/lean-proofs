import Mathlib

namespace Puzzling139335.ProperRotation

/-- The first crossing numerator is positive when the first acute angle
has cosine at most one half. Only the displayed source rows are needed. -/
theorem ns_pos_of_cos_le_half
    (c s d q a b u v w z : ℝ)
    (hc : 0 < c) (hc_half : c ≤ 1 / 2)
    (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hd : 0 < d) (hq : 0 < q) (hdq : d ^ 2 + q ^ 2 = 1)
    (_ha : 0 < a) (hb : 0 < b)
    (hv_lower : -(1 / 2 : ℝ) ≤ v)
    (hv_upper : v ≤ 1 / 2 - s - c * b)
    (hua : s * a ≤ u)
    (hface1 : s * u - c * v + c * (1 / 2 - b) ≤ 1 / 2)
    (hface2 : q * w + d * z + d * (1 / 2 - a) ≤ 1 / 2) :
    0 < q * (1 - u - w) - d * (v + z) := by
  have hc_sq_le : c ^ 2 ≤ c / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hc_half hc.le]
  have hs_one : s < 1 := by
    nlinarith only [hcs, hs, sq_pos_of_pos hc]
  have hs_half : (1 / 2 : ℝ) < s := by
    by_contra! h
    have hsq := mul_le_mul_of_nonneg_left h hs.le
    nlinarith only [hcs, hc_sq_le, hc_half, hsq, h]
  have hs_sq_le : s ^ 2 ≤ s := by
    nlinarith only [mul_le_mul_of_nonneg_left hs_one.le hs.le]
  have hone_sub_s : 1 - s ≤ c ^ 2 := by
    nlinarith only [hcs, hs_sq_le]
  have hcm_nonneg : 0 ≤ 1 - c := by
    linarith only [hc_half]
  have helim : s * u + (1 - c) * v ≤ 1 - s - c / 2 := by
    nlinarith only [hv_upper, hface1]
  have hv_weight :=
    mul_le_mul_of_nonneg_left hv_lower hcm_nonneg
  have hu_bound : s * u ≤ 3 / 2 - s - c := by
    nlinarith only [helim, hv_weight]
  have hu_rhs : 3 / 2 - s - c < s / 2 := by
    nlinarith only [hone_sub_s, hc_sq_le, hc]
  have hu_half : u < 1 / 2 := by
    apply (mul_lt_mul_iff_of_pos_left hs).mp
    nlinarith only [hu_bound, hu_rhs]
  have hv_simple : v ≤ 1 / 2 - s := by
    nlinarith only [hv_upper, mul_pos hc hb]
  have hsua := mul_le_mul_of_nonneg_left hua hs.le
  have hcircle_v := congrArg (fun t : ℝ => t * v) hcs
  have hsum_bound :
      s ^ 2 * (a + v) ≤ 1 - s - c / 2 + c * (1 - c) * v := by
    nlinarith only [helim, hsua, hcircle_v]
  have hv_weight' :=
    mul_le_mul_of_nonneg_left hv_simple (mul_nonneg hc.le hcm_nonneg)
  have hsum_I :
      s ^ 2 * (a + v) ≤ 1 - s - c ^ 2 / 2 - s * c * (1 - c) := by
    nlinarith only [hsum_bound, hv_weight']
  have hsc : c / 2 < s * c := by
    nlinarith only [mul_lt_mul_of_pos_right hs_half hc]
  have hcm_half : (1 / 2 : ℝ) ≤ 1 - c := by
    linarith only [hc_half]
  have hprod : c / 4 < s * c * (1 - c) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hcm_half (mul_pos hs hc).le
    nlinarith only [hsc, hmul]
  have hI_neg : 1 - s - c ^ 2 / 2 - s * c * (1 - c) < 0 := by
    nlinarith only [hone_sub_s, hc_sq_le, hprod]
  have hav_neg : a + v < 0 := by
    by_contra! h
    nlinarith only [hsum_I, hI_neg, mul_nonneg (sq_nonneg s) h]
  have hqd : 1 < q + d := by
    have hsum_pos : 0 < q + d := add_pos hq hd
    have hsum_sq : 1 < (q + d) ^ 2 := by
      nlinarith only [hdq, mul_pos hd hq]
    by_contra! h
    have hmul := mul_self_le_mul_self hsum_pos.le h
    nlinarith only [hsum_sq, hmul]
  have hq_gap : 0 < q * (1 / 2 - u) :=
    mul_pos hq (sub_pos.mpr hu_half)
  have hd_av : d * (a + v) < 0 := mul_neg_of_pos_of_neg hd hav_neg
  nlinarith only [hface2, hq_gap, hd_av, hqd]

end Puzzling139335.ProperRotation
