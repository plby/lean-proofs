import StackExchange.Puzzling139335.TwoSideFaces.NaturalBounds
import StackExchange.Puzzling139335.TwoSideFaces.SameHalfplane
import StackExchange.Puzzling139335.TwoSideFaces.Straddle
import StackExchange.Puzzling139335.TwoSideFaces.EndpointGeometry

/-!
# The excluded configurations of two source support faces

The theorems in this module take only scalar consequences of support,
source-box containment, and the two inverse-square tangent strips.  They
exclude both normals in either open vertical half-plane, the natural
straddling order, and reversed straddling order with normal dot product
at least one half.  All endpoint inequalities are inclusive where the
geometric argument permits equality.
-/

namespace Puzzling139335.TwoSideFaces

/-- The both-obtuse case is the reflected both-acute case, with the source
arms and the two physical side roles exchanged. -/
theorem same_obtuse_false (c s d q a b : ℝ)
    (hc : c < 0) (hs : 0 < s) (hd : d < 0) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (ha : 0 < a) (ha_half : a < 1 / 2)
    (hb : 0 < b) (hb_half : b < 1 / 2)
    (hvertical : (1 - 2 * b) * (-c) + (1 - 2 * a) * (-d) ≤ (1 - 2 * a) / 2)
    (hhorizontal : (1 - 2 * b) * s + (1 - 2 * a) * q ≤ 1)
    (hwidth1 : s - b * c ≤ 1) (hwidth2 : q - b * d ≤ 1) : False := by
  exact same_halfplane_false (-d) q (-c) s b a
    (neg_pos.mpr hd) hq (neg_pos.mpr hc) hs
    (by nlinarith only [hdq]) (by nlinarith only [hcs])
    hb hb_half ha ha_half
    (by nlinarith only [hvertical]) (by nlinarith only [hhorizontal])
    (by nlinarith only [hwidth2]) (by nlinarith only [hwidth1])

/-- In the natural straddling order, the individual face-height bounds
force the inclusive one-half dot-product bound. No such bound is assumed. -/
theorem natural_straddle_false (c s d q a b lam mu : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (ha_half : a < 1 / 2) (hb_half : b < 1 / 2)
    (hheight1 : b + (1 - 2 * b) * c ≤ 1 / 2)
    (hheight2 : a + (1 - 2 * a) * d ≤ 1 / 2)
    (hwidth1 : s + a * c ≤ 1) (hwidth2 : q + b * d ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (h₁ : lam + (s * q - c * d) * mu ≤ b - (s * q - c * d) * (1 - 2 * a))
    (h₂ : (s * q - c * d) * lam + mu ≤ a - (s * q - c * d) * (1 - 2 * b))
    (hspan : 1 ≤ (1 - 2 * b) * s / (2 * c) +
      (1 - 2 * a) * q / (2 * d) + lam * s + mu * q) : False := by
  obtain ⟨hc_one, hs_one⟩ := positive_circle_lt_one hc hs hcs
  obtain ⟨hd_one, hq_one⟩ := positive_circle_lt_one hd hq hdq
  have hc_half := cos_le_half_of_height hb_half hheight1
  have hd_half := cos_le_half_of_height ha_half hheight2
  have hdot := circle_dot_ge_half hc hs hd hq hcs hdq hc_half hd_half
  have ha_width := tangent_width_bound hc hs hcs hwidth1
  have hb_width := tangent_width_bound hd hq hdq hwidth2
  exact nearby_straddle_impossible c s d q a b (s * q - c * d) lam mu
    hc hc_one.le hs hs_one hd hd_one.le hq hq_one
    ha_half.le hb_half.le hdot ha_width hb_width hlam hmu h₁ h₂ hspan

/-- Reversed straddling faces with angular gap at most sixty degrees are
excluded by their equivalent inclusive normal-dot-product condition. -/
theorem reversed_small_gap_false (c s d q a b lam mu : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (ha_half : a ≤ 1 / 2) (hb_half : b ≤ 1 / 2)
    (hdot : 1 / 2 ≤ s * q - c * d)
    (hwidth1 : q + a * d ≤ 1) (hwidth2 : s + b * c ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (h₁ : lam + (s * q - c * d) * mu ≤ a - (s * q - c * d) * (1 - 2 * b))
    (h₂ : (s * q - c * d) * lam + mu ≤ b - (s * q - c * d) * (1 - 2 * a))
    (hspan : 1 ≤ (1 - 2 * b) * q / (2 * d) +
      (1 - 2 * a) * s / (2 * c) + lam * q + mu * s) : False := by
  obtain ⟨hc_one, hs_one⟩ := positive_circle_lt_one hc hs hcs
  obtain ⟨hd_one, hq_one⟩ := positive_circle_lt_one hd hq hdq
  have ha_width := tangent_width_bound hd hq hdq hwidth1
  have hb_width := tangent_width_bound hc hs hcs hwidth2
  exact reversed_nearby_straddle_impossible c s d q a b (s * q - c * d) lam mu
    hc hc_one.le hs hs_one hd hd_one.le hq hq_one
    ha_half hb_half hdot ha_width hb_width hlam hmu h₁ h₂ hspan

/-- The first natural face's own endpoint bounds force its entire rise above the right arm. -/
theorem right_face_height_of_endpoints {c s b Yx Yy : ℝ}
    (hc : 0 ≤ c) (hs : 0 < s) (hy : Yy ≤ 1 / 2)
    (hx : Yx + (1 - 2 * b) * s ≤ 1)
    (hsupport : c * (1 - Yx) ≤ s * (Yy - b)) :
    b + (1 - 2 * b) * c ≤ 1 / 2 := by
  have hxr : (1 - 2 * b) * s ≤ 1 - Yx := by linarith only [hx]
  have hcx := mul_le_mul_of_nonneg_left hxr hc
  have hscaled : s * ((1 - 2 * b) * c) ≤ s * (Yy - b) := by
    nlinarith only [hcx, hsupport]
  have hrise := le_of_mul_le_mul_left hscaled hs
  linarith only [hrise, hy]

/-- The corresponding endpoint statement for the natural left face. -/
theorem left_face_height_of_endpoints {d q a Zx Zy : ℝ}
    (hd : 0 ≤ d) (hq : 0 < q) (hy : Zy ≤ 1 / 2)
    (hx : 0 ≤ Zx - (1 - 2 * a) * q)
    (hsupport : d * Zx ≤ q * (Zy - a)) :
    a + (1 - 2 * a) * d ≤ 1 / 2 := by
  have hxl : (1 - 2 * a) * q ≤ Zx := by linarith only [hx]
  have hdx := mul_le_mul_of_nonneg_left hxl hd
  have hscaled : q * ((1 - 2 * a) * d) ≤ q * (Zy - a) := by
    nlinarith only [hdx, hsupport]
  have hrise := le_of_mul_le_mul_left hscaled hq
  linarith only [hrise, hy]

/-- The natural-order contradiction directly from endpoint support and strip
constraints. Gap coefficients, their positivity, face-height estimates, and
the horizontal span bound are all derived inside the proof. -/
theorem natural_straddle_false_of_endpoints (c s d q a b Yx Yy Zx Zy : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (ha_half : a < 1 / 2) (hb_half : b < 1 / 2)
    (hYy : Yy ≤ 1 / 2) (hZy : Zy ≤ 1 / 2)
    (hYlower : Yx + (1 - 2 * b) * s ≤ 1)
    (hZlower : 0 ≤ Zx - (1 - 2 * a) * q)
    (hR : c * (1 - Yx) ≤ s * (Yy - b))
    (hL : d * Zx ≤ q * (Zy - a))
    (hgap₁ : c * (Zx - Yx) + s * (Zy - Yy) ≤ 0)
    (hgap₂ : 0 ≤ -d * (Zx - Yx) + q * (Zy - Yy))
    (hwidth1 : s + a * c ≤ 1) (hwidth2 : q + b * d ≤ 1)
    (hstrip₁ :
      -s * ((Zx - (1 - 2 * a) * q) - (Yx + (1 - 2 * b) * s / 2)) +
        c * ((Zy - (1 - 2 * a) * d) - (Yy - (1 - 2 * b) * c / 2)) ≤ 1 / 2)
    (hstrip₂ :
      -(1 / 2 : ℝ) ≤
        -q * ((Yx + (1 - 2 * b) * s) - (Zx - (1 - 2 * a) * q / 2)) -
          d * ((Yy - (1 - 2 * b) * c) - (Zy - (1 - 2 * a) * d / 2))) : False := by
  have hheight1 := right_face_height_of_endpoints hc.le hs hYy hYlower hR
  have hheight2 := left_face_height_of_endpoints hd.le hq hZy hZlower hL
  obtain ⟨lam, mu, hlam, hmu, hgapx, hgapy⟩ :=
    gap_decomposition hc hs hd hq hgap₁ hgap₂
  have h₁ := crossed_strip_first hcs hgapx hgapy hstrip₁
  have h₂ := crossed_strip_second (a := a) (b := b) hdq hgapx hgapy
    (by simpa only [neg_div] using hstrip₂)
  have hspan := horizontal_bound hc hs hd hq hYy hZy hR hL hgapx
  exact natural_straddle_false c s d q a b lam mu hc hs hd hq hcs hdq
    ha_half hb_half hheight1 hheight2 hwidth1 hwidth2 hlam hmu h₁ h₂ hspan

/-- The reversed small-gap contradiction from facing endpoints and tangent
strips. The normal dot-product inequality includes equality. -/
theorem reversed_small_gap_false_of_endpoints (c s d q a b Yx Yy Zx Zy : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hcs : c ^ 2 + s ^ 2 = 1) (hdq : d ^ 2 + q ^ 2 = 1)
    (ha_half : a ≤ 1 / 2) (hb_half : b ≤ 1 / 2)
    (hdot : 1 / 2 ≤ s * q - c * d)
    (hYy : Yy ≤ 1 / 2) (hZy : Zy ≤ 1 / 2)
    (hR : d * (1 - Yx) ≤ q * (Yy - b))
    (hL : c * Zx ≤ s * (Zy - a))
    (hgap₁ : d * (Zx - Yx) + q * (Zy - Yy) ≤ 0)
    (hgap₂ : 0 ≤ -c * (Zx - Yx) + s * (Zy - Yy))
    (hwidth1 : q + a * d ≤ 1) (hwidth2 : s + b * c ≤ 1)
    (hstrip₁ :
      -q * ((Zx - (1 - 2 * b) * s) - (Yx + (1 - 2 * a) * q / 2)) +
        d * ((Zy - (1 - 2 * b) * c) - (Yy - (1 - 2 * a) * d / 2)) ≤ 1 / 2)
    (hstrip₂ :
      -(1 / 2 : ℝ) ≤
        -s * ((Yx + (1 - 2 * a) * q) - (Zx - (1 - 2 * b) * s / 2)) -
          c * ((Yy - (1 - 2 * a) * d) - (Zy - (1 - 2 * b) * c / 2))) : False := by
  obtain ⟨lam, mu, hlam, hmu, hgapx, hgapy⟩ :=
    gap_decomposition hd hq hc hs hgap₁ hgap₂
  have hfirst := crossed_strip_first (a := b) (b := a) hdq hgapx hgapy hstrip₁
  have hsecond := crossed_strip_second (a := b) (b := a) hcs hgapx hgapy
    (by simpa only [neg_div] using hstrip₂)
  have h₁ : lam + (s * q - c * d) * mu ≤ a - (s * q - c * d) * (1 - 2 * b) := by
    nlinarith only [hfirst]
  have h₂ : (s * q - c * d) * lam + mu ≤ b - (s * q - c * d) * (1 - 2 * a) := by
    nlinarith only [hsecond]
  have hspan := horizontal_bound hd hq hc hs hYy hZy hR hL hgapx
  exact reversed_small_gap_false c s d q a b lam mu hc hs hd hq hcs hdq
    ha_half hb_half hdot hwidth1 hwidth2 hlam hmu h₁ h₂ hspan

end Puzzling139335.TwoSideFaces
