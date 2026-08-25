import Mathlib

/-!
# Elementary scalar consequences of the N5 support geometry

These lemmas preserve the coordinates and lengths used by the geometric
argument.  They require no definitions of planar regions.
-/

namespace Puzzling139335.N5Facet

theorem prefix_face_impossible {t φ k b T j : ℝ}
    (ht : 0 < t) (ht4 : t < Real.pi / 4) (hφ : 0 < φ) (hφt : φ < t)
    (hk : k < Real.cos t) (hb : 0 < b) (hj : 0 < j)
    (hJT : j + T = 1 - b)
    (hvertical : b + j * Real.cos φ + T * Real.cos t ≤ k) : False := by
  have hcos : Real.cos t < Real.cos φ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hφ.le (by linarith [Real.pi_pos]) hφt
  have hc1 : Real.cos t < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := t) (by norm_num) (by linarith [Real.pi_pos]) ht
    simpa only [Real.cos_zero] using h
  have hgap := mul_pos hj (sub_pos.mpr hcos)
  have hleg := mul_pos hb (sub_pos.mpr hc1)
  have hlength := congrArg (fun x : ℝ => Real.cos t * x) hJT
  nlinarith only [hvertical, hk, hgap, hleg, hlength]

theorem outgoing_aligned_face_impossible {j L T : ℝ}
    (hT : 0 < T) (hj : j = L - T) (hface : j = L) : False := by
  linarith

theorem side_fit_lt_ratio {c s b d : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hunit : c ^ 2 + s ^ 2 = 1) (hfit : c + s * b ≤ d) (hd : d < 1) :
    b < s / (1 + c) := by
  have hden : 0 < 1 + c := by linarith
  apply (lt_div_iff₀ hden).mpr
  have hm := mul_lt_mul_of_pos_right (show s * b < 1 - c by linarith) hden
  have hm' : s * (b * (1 + c)) < s * s := by
    nlinarith only [hm, hunit]
  exact lt_of_mul_lt_mul_left hm' hs.le

theorem leg_lt_length_mul_sine {b L c s : ℝ}
    (hb : 0 < b) (hL : L = 1 - b) (hc : 0 < c) (hsc : s < c)
    (hbound : b < s / (1 + c)) : b < L * s := by
  have hden : 0 < 1 + c := by linarith
  have hmul := (lt_div_iff₀ hden).mp hbound
  have hgap := mul_pos hb (sub_pos.mpr hsc)
  rw [hL]
  nlinarith only [hmul, hgap]

theorem wrong_right_arm_impossible {c s h k b L : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hc1 : c < 1) (hb : 0 < b)
    (hL : L = 1 - b) (hk : k < c)
    (hendpoint : h + L * s ≤ 1)
    (hsupport : c * (1 - h) + s * (b - k) ≤ 0) : False := by
  have hscaled := mul_le_mul_of_nonneg_left hendpoint hc.le
  have hlower : s * (b + c * L) ≤ s * k := by
    nlinarith only [hscaled, hsupport]
  have hleg : c < b + c * L := by
    rw [hL]
    nlinarith only [mul_pos hb (sub_pos.mpr hc1)]
  have hstrict := mul_lt_mul_of_pos_left (hk.trans hleg) hs
  linarith

theorem surviving_right_arm_excludes_center {c s h k b L : ℝ}
    (hsc : s < c) (hh : h < c) (hb : b < 1 / 2) (hL : L = 1 - b)
    (hendpoint : L * (c - s) ≤ h - k) : k < (c + s) / 2 := by
  have hgap := mul_pos (sub_pos.mpr hsc) (show 0 < 1 / 2 - b by linarith)
  rw [hL] at hendpoint
  nlinarith only [hendpoint, hh, hgap]

theorem top_hull_face_lt_remaining_length {c s h k b L H : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hc1 : c < 1) (hb : 0 < b)
    (hL : L = 1 - b) (hk : k < c)
    (hendpoint : h + s * H ≤ 1)
    (hsupport : c * (1 - h) ≤ s * (k - b)) : H < L := by
  have hscaled := mul_le_mul_of_nonneg_left hendpoint hc.le
  have hbound : s * (c * H) ≤ s * (k - b) := by
    nlinarith only [hscaled, hsupport]
  have hcH : c * H ≤ k - b := by
    by_contra h
    have hm := mul_lt_mul_of_pos_left (lt_of_not_ge h) hs
    linarith
  have hleg : 0 < b * (1 - c) := mul_pos hb (sub_pos.mpr hc1)
  have htarget : c * H < c * L := by
    rw [hL]
    nlinarith only [hcH, hk, hleg]
  exact lt_of_mul_lt_mul_left htarget hc.le

end Puzzling139335.N5Facet
