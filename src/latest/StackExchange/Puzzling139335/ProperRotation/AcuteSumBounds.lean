import Mathlib

namespace Puzzling139335.ProperRotation

/-- Every positive component of either unit-circle pair is strictly below one. -/
theorem acute_components_lt_one
    (c s d q : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1) :
    c < 1 ∧ s < 1 ∧ d < 1 ∧ q < 1 := by
  constructor
  · nlinarith only [hcs, hc, sq_pos_of_pos hs]
  constructor
  · nlinarith only [hcs, hs, sq_pos_of_pos hc]
  constructor
  · nlinarith only [hdq, hd, sq_pos_of_pos hq]
  · nlinarith only [hdq, hq, sq_pos_of_pos hd]

private theorem sine_le_cosine_of_acute_sum
    (c s d q : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (hacute : 0 ≤ c * d - s * q) :
    s ≤ d := by
  have hfactor :
      (c * d - s * q) * (c * d + s * q) = d ^ 2 - s ^ 2 := by
    calc
      (c * d - s * q) * (c * d + s * q) =
          d ^ 2 * (c ^ 2 + s ^ 2) - s ^ 2 * (d ^ 2 + q ^ 2) := by
        ring
      _ = d ^ 2 - s ^ 2 := by rw [hcs, hdq]; ring
  have hnonneg : 0 ≤ d ^ 2 - s ^ 2 := by
    rw [← hfactor]
    exact mul_nonneg hacute (add_pos (mul_pos hc hd) (mul_pos hs hq)).le
  by_contra! h
  have hpos := mul_pos (sub_pos.mpr h) (add_pos hs hd)
  nlinarith only [hnonneg, hpos]

/-- Coarse bounds for the ordered acute-sum frame, derived entirely from
the circle identities, the cosine order, and the product bound. -/
theorem ordered_acute_sum_bounds
    (c s d q : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (horder : c ≤ d) (hprod : 4 * c * d ≤ 1)
    (hacute : 0 ≤ c * d - s * q) :
    c < 3 / 10 ∧ 9 / 10 < s ∧ 9 / 10 < d ∧
      s ≤ d ∧ s ≤ s * d + c * q ∧ 1 < c + s := by
  have hsd : s ≤ d :=
    sine_le_cosine_of_acute_sum c s d q hc hs hd hq hcs hdq hacute
  obtain ⟨hc_one, hs_one, hd_one, hq_one⟩ :=
    acute_components_lt_one c s d q hc hs hd hq hcs hdq
  have hfour_csq : 4 * c ^ 2 ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left horder hc.le
    nlinarith only [hprod, hmul]
  have hs_five_sixths : (5 / 6 : ℝ) < s := by
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_left h hs.le
    nlinarith only [hfour_csq, hcs, hmul, h]
  have hfour_cs : 4 * c * s ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hsd hc.le
    nlinarith only [hprod, hmul]
  have hc_three_tenths : c < 3 / 10 := by
    have hmul := mul_lt_mul_of_pos_right hs_five_sixths hc
    nlinarith only [hfour_cs, hmul]
  have hc_sq_small : c ^ 2 < 9 / 100 := by
    have hmul := mul_self_lt_mul_self hc.le hc_three_tenths
    nlinarith only [hmul]
  have hs_nine_tenths : (9 / 10 : ℝ) < s := by
    by_contra! h
    have hmul := mul_le_mul_of_nonneg_left h hs.le
    nlinarith only [hcs, hc_sq_small, hmul, h]
  have hd_nine_tenths : (9 / 10 : ℝ) < d :=
    lt_of_lt_of_le hs_nine_tenths hsd
  have hqc_sq : q ^ 2 ≤ c ^ 2 := by
    have hmul := mul_self_le_mul_self hs.le hsd
    nlinarith only [hcs, hdq, hmul]
  have hqc : q ≤ c := by
    by_contra! h
    have hpos := mul_pos (sub_pos.mpr h) (add_pos hq hc)
    nlinarith only [hqc_sq, hpos]
  have hdelta : s ≤ s * d + c * q := by
    have hfirst : 0 ≤ q * (c - q) :=
      mul_nonneg hq.le (sub_nonneg.mpr hqc)
    have hsecond : 0 ≤ (1 - d) * (1 + d - s) := by
      apply mul_nonneg (sub_nonneg.mpr hd_one.le)
      linarith only [hd, hs_one]
    nlinarith only [hdq, hfirst, hsecond]
  have hsum : 1 < c + s := by
    have hsum_pos : 0 < c + s := add_pos hc hs
    have hsum_sq : 1 < (c + s) ^ 2 := by
      nlinarith only [hcs, mul_pos hc hs]
    by_contra! h
    have hmul := mul_self_le_mul_self hsum_pos.le h
    nlinarith only [hsum_sq, hmul]
  exact ⟨hc_three_tenths, hs_nine_tenths, hd_nine_tenths, hsd, hdelta, hsum⟩

end Puzzling139335.ProperRotation
