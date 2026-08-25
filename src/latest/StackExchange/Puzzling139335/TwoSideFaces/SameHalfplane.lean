import Mathlib

namespace Puzzling139335.TwoSideFaces

private theorem component_lt_one
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hcircle : x ^ 2 + y ^ 2 = 1) :
    x < 1 ∧ y < 1 := by
  constructor
  · nlinarith only [hcircle, hx, sq_pos_of_pos hy]
  · nlinarith only [hcircle, hy, sq_pos_of_pos hx]

private theorem circle_sum_gt_one
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hcircle : x ^ 2 + y ^ 2 = 1) :
    1 < x + y := by
  have hpos : 0 < x + y := add_pos hx hy
  have hsq : 1 < (x + y) ^ 2 := by
    nlinarith only [hcircle, mul_pos hx hy]
  by_contra! h
  have hmul := mul_self_le_mul_self hpos.le h
  nlinarith only [hsq, hmul]

private theorem other_component_gt_half
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hcircle : x ^ 2 + y ^ 2 = 1) (hx_half : x < 1 / 2) :
    (1 / 2 : ℝ) < y := by
  by_contra! h
  have hmx := mul_le_mul_of_nonneg_left hx_half.le hx.le
  have hmy := mul_le_mul_of_nonneg_left h hy.le
  nlinarith only [hcircle, hmx, hmy, hx_half, h]

private theorem scaled_width_bound
    (x y a : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hcircle : x ^ 2 + y ^ 2 = 1) (hwidth : y + a * x ≤ 1) :
    a * (1 + y) ≤ x := by
  have hfactor : 0 ≤ 1 + y := by linarith only [hy]
  have hmul := mul_le_mul_of_nonneg_left hwidth hfactor
  apply (mul_le_mul_iff_of_pos_left hx).mp
  nlinarith only [hmul, hcircle]

private theorem opposite_circle_order
    (c s d q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (horder : c ≤ d) :
    q ≤ s := by
  have hmul := mul_self_le_mul_self hc horder
  apply (sq_le_sq₀ hq hs).mp
  nlinarith only [hcs, hdq, hmul]

private theorem circle_chord_lower_bound
    (c s d q : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (horder : c ≤ d) :
    s ≤ s * d + (1 - c) * q := by
  obtain ⟨hc_one, _⟩ := component_lt_one c s hc hs hcs
  obtain ⟨hd_one, _⟩ := component_lt_one d q hd hq hdq
  have hc_nonneg : 0 ≤ 1 - c := sub_nonneg.mpr hc_one.le
  have hd_nonneg : 0 ≤ 1 - d := sub_nonneg.mpr hd_one.le
  have hq_sq : q ^ 2 = 1 - d ^ 2 := by linarith only [hdq]
  have hs_sq : s ^ 2 = 1 - c ^ 2 := by linarith only [hcs]
  have hid :
      ((1 - c) * q) ^ 2 - (s * (1 - d)) ^ 2 =
        2 * (1 - c) * (1 - d) * (d - c) := by
    calc
      ((1 - c) * q) ^ 2 - (s * (1 - d)) ^ 2 =
          (1 - c) ^ 2 * q ^ 2 - s ^ 2 * (1 - d) ^ 2 := by ring
      _ = (1 - c) ^ 2 * (1 - d ^ 2) - (1 - c ^ 2) * (1 - d) ^ 2 := by
        rw [hq_sq, hs_sq]
      _ = 2 * (1 - c) * (1 - d) * (d - c) := by ring
  have hnonneg : 0 ≤ 2 * (1 - c) * (1 - d) * (d - c) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hc_nonneg) hd_nonneg)
      (sub_nonneg.mpr horder)
  have hsq :
      (s * (1 - d)) ^ 2 ≤ ((1 - c) * q) ^ 2 := by
    linarith only [hid, hnonneg]
  have hroot : s * (1 - d) ≤ (1 - c) * q :=
    (sq_le_sq₀ (mul_nonneg hs.le hd_nonneg) (mul_nonneg hc_nonneg hq.le)).mp hsq
  nlinarith only [hroot]

private theorem first_order_false
    (c s d q a : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (horder : c ≤ d) (hwidth : a * (1 + s) ≤ c)
    (hlpos : 0 < 1 - 2 * a)
    (hbound : (1 - 2 * a) * (2 * s * d + (1 - 2 * c) * q) ≤ 1 - 2 * c) :
    False := by
  let l := 1 - 2 * a
  let k := 1 - 2 * c
  let F := 2 * s * d + k * q
  change 0 < l at hlpos
  change l * F ≤ k at hbound
  have hqs : q ≤ s :=
    opposite_circle_order c s d q hs.le hq.le hc.le hcs hdq horder
  have hchord := circle_chord_lower_bound c s d q hc hs hd hq hcs hdq horder
  have hF : s ≤ F := by
    dsimp [F, k]
    nlinarith only [hchord, hqs]
  have hid :
      (1 + s) * (l * s - k) = c * (2 - c) + 2 * s * (c - a * (1 + s)) := by
    dsimp [l, k]
    nlinarith only [hcs]
  obtain ⟨hc_one, _⟩ := component_lt_one c s hc hs hcs
  have hbase : 0 < c * (2 - c) := by
    apply mul_pos hc
    linarith only [hc_one]
  have hrem : 0 ≤ 2 * s * (c - a * (1 + s)) :=
    mul_nonneg (mul_pos (by norm_num) hs).le (sub_nonneg.mpr hwidth)
  have hpositive : 0 < (1 + s) * (l * s - k) := by
    linarith only [hid, hbase, hrem]
  have hls : k < l * s := by
    by_contra! h
    have hnonpos : (1 + s) * (l * s - k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith only [hs]) (sub_nonpos.mpr h)
    linarith only [hpositive, hnonpos]
  have hmul := mul_le_mul_of_nonneg_left hF hlpos.le
  linarith only [hls, hmul, hbound]

private theorem second_order_false
    (c s d q a : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (hc_half : c < 1 / 2) (horder : d ≤ c)
    (hwidth : a * (1 + q) ≤ d)
    (hbound : (1 - 2 * a) * (2 * s * d + (1 - 2 * c) * q) ≤ 1 - 2 * c) :
    False := by
  let l := 1 - 2 * a
  let k := 1 - 2 * c
  let F := 2 * s * d + k * q
  let A := 1 + q - 2 * d
  let B := d + 2 * q
  let J := 2 * A * s + 2 * B * c - B
  change l * F ≤ k at hbound
  have hd_half : d < 1 / 2 := lt_of_le_of_lt horder hc_half
  have hs_half := other_component_gt_half c s hc hs hcs hc_half
  have hq_half := other_component_gt_half d q hd hq hdq hd_half
  have hsum_order : c + d ≤ q + s := by
    linarith only [hc_half, hd_half, hs_half, hq_half]
  have hfactor : (q - s) * (q + s) = (c - d) * (c + d) := by
    nlinarith only [hcs, hdq]
  have hdiff : q - s ≤ c - d := by
    have hmul :=
      mul_le_mul_of_nonneg_left hsum_order (sub_nonneg.mpr horder)
    apply (mul_le_mul_iff_of_pos_right (add_pos hq hs)).mp
    nlinarith only [hfactor, hmul]
  have hslower : q + d - c ≤ s := by linarith only [hdiff]
  have hA : 0 < A := by
    dsimp [A]
    linarith only [hq, hd_half]
  have hqd : 1 < q + d := by
    have h := circle_sum_gt_one d q hd hq hdq
    linarith only [h]
  have hcoef : 0 < 3 * d + q - 1 := by
    linarith only [hqd, hd]
  have hJ_bound : 2 - d + 2 * (3 * d + q - 1) * (c - d) ≤ J := by
    have hmul :=
      mul_le_mul_of_nonneg_left hslower
        (mul_pos (show (0 : ℝ) < 2 by norm_num) hA).le
    dsimp [J, A, B] at hmul ⊢
    nlinarith only [hmul, hdq]
  have hterm : 0 ≤ 2 * (3 * d + q - 1) * (c - d) :=
    mul_nonneg (mul_pos (by norm_num) hcoef).le (sub_nonneg.mpr horder)
  have hJ : 0 < J := by
    linarith only [hJ_bound, hterm, hd_half]
  have hk : 0 < k := by
    dsimp [k]
    linarith only [hc_half]
  have hF : 0 < F := by
    dsimp [F]
    exact add_pos (mul_pos (mul_pos (by norm_num) hs) hd) (mul_pos hk hq)
  have hlower : A ≤ (1 + q) * l := by
    dsimp [A, l]
    nlinarith only [hwidth]
  have hinner : A * q - (1 + q) = -d * B := by
    dsimp [A, B]
    nlinarith only [hdq]
  have hid : A * F - k * (1 + q) = d * J := by
    calc
      A * F - k * (1 + q) = 2 * A * s * d + k * (A * q - (1 + q)) := by
        dsimp [F]
        ring
      _ = 2 * A * s * d + k * (-d * B) := by rw [hinner]
      _ = d * J := by dsimp [k, J]; ring
  have hmul := mul_le_mul_of_nonneg_right hlower hF.le
  have hJ_le : d * J ≤ (1 + q) * (l * F - k) := by
    rw [← hid]
    nlinarith only [hmul]
  have hnonpos : (1 + q) * (l * F - k) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith only [hq]) (sub_nonpos.mpr hbound)
  have hpositive := lt_of_lt_of_le (mul_pos hd hJ) hJ_le
  exact (not_lt_of_ge hnonpos) hpositive

/-- The two distinct acute face normals cannot satisfy their vertical and
horizontal variation bounds together with both raw source-width bounds. -/
theorem same_halfplane_false
    (c s d q a b : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (_ha : 0 < a) (ha_half : a < 1 / 2)
    (_hb : 0 < b) (hb_half : b < 1 / 2)
    (hvertical :
      (1 - 2 * b) * c + (1 - 2 * a) * d ≤ (1 - 2 * b) / 2)
    (hhorizontal : (1 - 2 * b) * s + (1 - 2 * a) * q ≤ 1)
    (hwidth1 : s + a * c ≤ 1) (hwidth2 : q + a * d ≤ 1) :
    False := by
  let r := 1 - 2 * b
  let l := 1 - 2 * a
  let k := 1 - 2 * c
  let F := 2 * s * d + k * q
  change r * c + l * d ≤ r / 2 at hvertical
  change r * s + l * q ≤ 1 at hhorizontal
  have hr : 0 < r := by dsimp [r]; linarith only [hb_half]
  have hl : 0 < l := by dsimp [l]; linarith only [ha_half]
  have hc_half : c < 1 / 2 := by
    apply (mul_lt_mul_iff_of_pos_left hr).mp
    nlinarith only [hvertical, mul_pos hl hd]
  have hk : 0 < k := by dsimp [k]; linarith only [hc_half]
  have hver : 2 * l * d ≤ r * k := by
    dsimp [k]
    nlinarith only [hvertical]
  have hbound : l * F ≤ k := by
    have hmulv := mul_le_mul_of_nonneg_left hver hs.le
    have hmulh := mul_le_mul_of_nonneg_left hhorizontal hk.le
    dsimp [F]
    nlinarith only [hmulv, hmulh]
  have hwidth_c := scaled_width_bound c s a hc hs hcs hwidth1
  have hwidth_d := scaled_width_bound d q a hd hq hdq hwidth2
  rcases le_total c d with horder | horder
  · exact first_order_false c s d q a hc hs hd hq hcs hdq horder hwidth_c hl hbound
  · exact second_order_false c s d q a hc hs hd hq hcs hdq hc_half horder hwidth_d
      hbound

end Puzzling139335.TwoSideFaces
