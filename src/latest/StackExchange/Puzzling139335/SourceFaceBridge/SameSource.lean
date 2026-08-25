import StackExchange.Puzzling139335.SourceFaceBridge.UpperDefs
import StackExchange.Puzzling139335.TwoSideFaces

/-!
# Actual source faces in the same open vertical half-plane

Cross-support inequalities order the facing endpoints of distinct support
faces.  The resulting nonnegative vertical gap and nonpositive horizontal
gap imply the two total span bounds directly from endpoint containment.
No convex-hull boundary ordering or variation hypothesis is assumed.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

private theorem ordered_face_spans
    (c s d q r l b X₁ Y₁ X₂ Y₂ : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hdet : 0 < c * q - s * d)
    (hfirst_right : X₁ + r * s ≤ 1)
    (hsecond_left : 0 ≤ X₂ - l * q)
    (hsecond_top : Y₂ + l * d ≤ 1 / 2)
    (hleg : c + s * b ≤ c * X₁ + s * Y₁)
    (hcross₁ : c * (X₂ + l * q) + s * (Y₂ - l * d) ≤ c * X₁ + s * Y₁)
    (hcross₂ : d * (X₁ - r * s) + q * (Y₁ + r * c) ≤ d * X₂ + q * Y₂) :
    2 * r * c + 2 * l * d ≤ 1 / 2 - b ∧ 2 * r * s + 2 * l * q ≤ 1 := by
  let gx := (X₂ + l * q) - (X₁ - r * s)
  let gy := (Y₂ - l * d) - (Y₁ + r * c)
  have hgap₁ : c * gx + s * gy ≤ 0 := by
    dsimp [gx, gy]
    nlinarith only [hcross₁]
  have hgap₂ : 0 ≤ d * gx + q * gy := by
    dsimp [gx, gy]
    nlinarith only [hcross₂]
  have hgy : 0 ≤ gy := by
    have hc₂ := mul_nonneg hc.le hgap₂
    have hd₁ := mul_nonpos_of_nonneg_of_nonpos hd.le hgap₁
    have hscaled : (c * q - s * d) * 0 ≤ (c * q - s * d) * gy := by
      nlinarith only [hc₂, hd₁]
    exact le_of_mul_le_mul_left hscaled hdet
  have hgx : gx ≤ 0 := by
    have hq₁ := mul_nonpos_of_nonneg_of_nonpos hq.le hgap₁
    have hs₂ := mul_nonneg hs.le hgap₂
    have hscaled : (c * q - s * d) * gx ≤ (c * q - s * d) * 0 := by
      nlinarith only [hq₁, hs₂]
    exact le_of_mul_le_mul_left hscaled hdet
  have hbottom : b ≤ Y₁ - r * c := by
    have hcx := mul_le_mul_of_nonneg_left hfirst_right hc.le
    have hscaled : s * b ≤ s * (Y₁ - r * c) := by
      nlinarith only [hcx, hleg]
    exact le_of_mul_le_mul_left hscaled hs
  dsimp [gx] at hgx
  dsimp [gy] at hgy
  constructor
  · nlinarith only [hbottom, hgy, hsecond_top]
  · nlinarith only [hfirst_right, hsecond_left, hgx]

private theorem same_quadrant_face_spans
    (c s d q r l b X₁ Y₁ X₂ Y₂ : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) (hq : 0 < q)
    (hdet : c * q - s * d ≠ 0)
    (hfirst_right : X₁ + r * s ≤ 1) (hfirst_left : 0 ≤ X₁ - r * s)
    (hfirst_top : Y₁ + r * c ≤ 1 / 2)
    (hsecond_right : X₂ + l * q ≤ 1) (hsecond_left : 0 ≤ X₂ - l * q)
    (hsecond_top : Y₂ + l * d ≤ 1 / 2)
    (hleg₁ : c + s * b ≤ c * X₁ + s * Y₁)
    (hleg₂ : d + q * b ≤ d * X₂ + q * Y₂)
    (hcross₁minus : c * (X₂ + l * q) + s * (Y₂ - l * d) ≤ c * X₁ + s * Y₁)
    (hcross₁plus : c * (X₂ - l * q) + s * (Y₂ + l * d) ≤ c * X₁ + s * Y₁)
    (hcross₂minus : d * (X₁ + r * s) + q * (Y₁ - r * c) ≤ d * X₂ + q * Y₂)
    (hcross₂plus : d * (X₁ - r * s) + q * (Y₁ + r * c) ≤ d * X₂ + q * Y₂) :
    2 * r * c + 2 * l * d ≤ 1 / 2 - b ∧ 2 * r * s + 2 * l * q ≤ 1 := by
  rcases lt_or_gt_of_ne hdet with hnegative | hpositive
  · have hswap := ordered_face_spans d q c s l r b X₂ Y₂ X₁ Y₁
      hd hq hc hs (by nlinarith only [hnegative])
      hsecond_right hfirst_left hfirst_top hleg₂ hcross₂minus hcross₁plus
    exact ⟨by nlinarith only [hswap.1], by nlinarith only [hswap.2]⟩
  · exact ordered_face_spans c s d q r l b X₁ Y₁ X₂ Y₂ hc hs hd hq hpositive
      hfirst_right hsecond_left hsecond_top hleg₁ hcross₁minus hcross₂plus

namespace UpperSupportedSource

variable {d : UpperFaceData} {reversed : Bool} {P : Set Plane}

/-- Distinct normals in the open upper half-plane are not parallel. -/
theorem normal_det_ne (h : UpperSupportedSource d reversed P) (hne : d.φ ≠ d.ψ) :
    Real.cos d.φ * Real.sin d.ψ - Real.sin d.φ * Real.cos d.ψ ≠ 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsin : 0 < Real.sin (d.ψ - d.φ) :=
      Real.sin_pos_of_mem_Ioo ⟨sub_pos.mpr hlt, by linarith [h.psi_lt_pi, h.phi_pos]⟩
    rw [Real.sin_sub] at hsin
    intro hz
    nlinarith only [hsin, hz]
  · have hsin : 0 < Real.sin (d.φ - d.ψ) :=
      Real.sin_pos_of_mem_Ioo ⟨sub_pos.mpr hgt, by linarith [h.phi_lt_pi, h.psi_pos]⟩
    rw [Real.sin_sub] at hsin
    intro hz
    nlinarith only [hsin, hz]

/-- Actual endpoints and support inequalities give both total face spans
when both upper normals point right. -/
theorem same_acute_spans (h : UpperSupportedSource d reversed P)
    (hφ : d.φ < Real.pi / 2) (hψ : d.ψ < Real.pi / 2) (hne : d.φ ≠ d.ψ) :
    (1 - 2 * d.b) * Real.cos d.φ + (1 - 2 * d.a) * Real.cos d.ψ ≤ 1 / 2 - d.b ∧
      (1 - 2 * d.b) * Real.sin d.φ + (1 - 2 * d.a) * Real.sin d.ψ ≤ 1 := by
  have hπ := Real.pi_pos
  have hc : 0 < Real.cos d.φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [h.phi_pos], hφ⟩
  have hs : 0 < Real.sin d.φ := Real.sin_pos_of_mem_Ioo ⟨h.phi_pos, h.phi_lt_pi⟩
  have hd : 0 < Real.cos d.ψ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [h.psi_pos], hψ⟩
  have hq : 0 < Real.sin d.ψ := Real.sin_pos_of_mem_Ioo ⟨h.psi_pos, h.psi_lt_pi⟩
  have hb₁ := h.source_subset h.face₁minus_mem
  have hb₂ := h.source_subset h.face₁plus_mem
  have hb₃ := h.source_subset h.face₂minus_mem
  have hb₄ := h.source_subset h.face₂plus_mem
  have hleg := h.source_supports h.right_top_mem
  have hc₁ := (h.source_supports h.face₂minus_mem).1
  have hc₂ := (h.source_supports h.face₂plus_mem).1
  have hc₃ := (h.source_supports h.face₁minus_mem).2
  have hc₄ := (h.source_supports h.face₁plus_mem).2
  have hspans := same_quadrant_face_spans
    (Real.cos d.φ) (Real.sin d.φ) (Real.cos d.ψ) (Real.sin d.ψ)
    (1 / 2 - d.b) (1 / 2 - d.a) d.b (d.M₁ 0) (d.M₁ 1) (d.M₂ 0) (d.M₂ 1)
    hc hs hd hq (h.normal_det_ne hne)
    hb₁.1.2 hb₂.1.1 hb₂.2.2 hb₃.1.2 hb₄.1.1 hb₄.2.2
    (by simpa [UpperFaceData.normal₁] using hleg.1)
    (by simpa [UpperFaceData.normal₂] using hleg.2)
    hc₁ hc₂ hc₃ hc₄
  exact ⟨by nlinarith only [hspans.1], by nlinarith only [hspans.2]⟩

/-- Horizontal reflection of the endpoint argument gives the spans when
both upper normals point left. -/
theorem same_obtuse_spans (h : UpperSupportedSource d reversed P)
    (hφ : Real.pi / 2 < d.φ) (hψ : Real.pi / 2 < d.ψ) (hne : d.φ ≠ d.ψ) :
    (1 - 2 * d.b) * (-Real.cos d.φ) + (1 - 2 * d.a) * (-Real.cos d.ψ) ≤
        1 / 2 - d.a ∧
      (1 - 2 * d.b) * Real.sin d.φ + (1 - 2 * d.a) * Real.sin d.ψ ≤ 1 := by
  have hπ := Real.pi_pos
  have hc : 0 < -Real.cos d.φ := neg_pos.mpr
    (Real.cos_neg_of_pi_div_two_lt_of_lt hφ (by linarith [h.phi_lt_pi]))
  have hs : 0 < Real.sin d.φ := Real.sin_pos_of_mem_Ioo ⟨h.phi_pos, h.phi_lt_pi⟩
  have hd : 0 < -Real.cos d.ψ := neg_pos.mpr
    (Real.cos_neg_of_pi_div_two_lt_of_lt hψ (by linarith [h.psi_lt_pi]))
  have hq : 0 < Real.sin d.ψ := Real.sin_pos_of_mem_Ioo ⟨h.psi_pos, h.psi_lt_pi⟩
  have hb₁ := h.source_subset h.face₁minus_mem
  have hb₂ := h.source_subset h.face₁plus_mem
  have hb₃ := h.source_subset h.face₂minus_mem
  have hb₄ := h.source_subset h.face₂plus_mem
  dsimp [lowerHalfSquare, UpperFaceData.face₁minus, UpperFaceData.face₁plus,
    UpperFaceData.face₂minus, UpperFaceData.face₂plus] at hb₁ hb₂ hb₃ hb₄
  have hleg := h.source_supports h.left_top_mem
  have hc₁ := (h.source_supports h.face₂minus_mem).1
  have hc₂ := (h.source_supports h.face₂plus_mem).1
  have hc₃ := (h.source_supports h.face₁minus_mem).2
  have hc₄ := (h.source_supports h.face₁plus_mem).2
  dsimp [UpperFaceData.normal₁, UpperFaceData.normal₂, UpperFaceData.face₁minus,
    UpperFaceData.face₁plus, UpperFaceData.face₂minus, UpperFaceData.face₂plus]
    at hleg hc₁ hc₂ hc₃ hc₄
  have hdet : (-Real.cos d.φ) * Real.sin d.ψ - Real.sin d.φ * (-Real.cos d.ψ) ≠ 0 := by
    intro hz
    apply h.normal_det_ne hne
    nlinarith only [hz]
  have hspans := same_quadrant_face_spans
    (-Real.cos d.φ) (Real.sin d.φ) (-Real.cos d.ψ) (Real.sin d.ψ)
    (1 / 2 - d.b) (1 / 2 - d.a) d.a (1 - d.M₁ 0) (d.M₁ 1) (1 - d.M₂ 0) (d.M₂ 1)
    hc hs hd hq hdet
    (by nlinarith only [hb₂.1.1]) (by nlinarith only [hb₁.1.2])
    (by nlinarith only [hb₁.2.2])
    (by nlinarith only [hb₄.1.1]) (by nlinarith only [hb₃.1.2])
    (by nlinarith only [hb₃.2.2])
    (by nlinarith only [hleg.1]) (by nlinarith only [hleg.2])
    (by nlinarith only [hc₂]) (by nlinarith only [hc₁])
    (by nlinarith only [hc₄]) (by nlinarith only [hc₃])
  exact ⟨by nlinarith only [hspans.1], by nlinarith only [hspans.2]⟩

/-- Either tangent functional has range of width at most one on the source. -/
theorem tangent_span_le_one (h : UpperSupportedSource d reversed P)
    {p q : Plane} (hp : p ∈ P) (hq : q ∈ P) :
    d.tangent₁ p - d.tangent₁ q ≤ 1 ∧ d.tangent₂ p - d.tangent₂ q ≤ 1 := by
  have h₁p := (h.right_inverse_box hp).2.2.2
  have h₁q := (h.right_inverse_box hq).2.2.1
  have h₂p := (h.left_inverse_box hp).2.2.2
  have h₂q := (h.left_inverse_box hq).2.2.1
  exact ⟨by linarith only [h₁p, h₁q], by linarith only [h₂p, h₂q]⟩

/-- The actual base endpoints and leg tops give the four raw tangent-width bounds. -/
theorem source_widths (h : UpperSupportedSource d reversed P) :
    (Real.sin d.φ + d.a * Real.cos d.φ ≤ 1 ∧
      Real.sin d.ψ + d.a * Real.cos d.ψ ≤ 1) ∧
    (Real.sin d.φ - d.b * Real.cos d.φ ≤ 1 ∧
      Real.sin d.ψ - d.b * Real.cos d.ψ ≤ 1) := by
  have hleft := h.tangent_span_le_one h.left_top_mem (h.base_mem 1 (by norm_num))
  have hright := h.tangent_span_le_one (h.base_mem 0 (by norm_num)) h.right_top_mem
  dsimp [UpperFaceData.tangent₁, UpperFaceData.tangent₂] at hleft hright
  exact ⟨⟨by nlinarith only [hleft.1], by nlinarith only [hleft.2]⟩,
    ⟨by nlinarith only [hright.1], by nlinarith only [hright.2]⟩⟩

/-- Two distinct acute upper normals cannot occur in actual supported source data. -/
theorem same_acute_false (h : UpperSupportedSource d reversed P)
    (hφ : d.φ < Real.pi / 2) (hψ : d.ψ < Real.pi / 2) (hne : d.φ ≠ d.ψ) : False := by
  have hπ := Real.pi_pos
  have hspans := h.same_acute_spans hφ hψ hne
  have hwidths := h.source_widths
  exact TwoSideFaces.same_halfplane_false
    (Real.cos d.φ) (Real.sin d.φ) (Real.cos d.ψ) (Real.sin d.ψ) d.a d.b
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [h.phi_pos], hφ⟩)
    (Real.sin_pos_of_mem_Ioo ⟨h.phi_pos, h.phi_lt_pi⟩)
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [h.psi_pos], hψ⟩)
    (Real.sin_pos_of_mem_Ioo ⟨h.psi_pos, h.psi_lt_pi⟩)
    (Real.cos_sq_add_sin_sq d.φ) (Real.cos_sq_add_sin_sq d.ψ)
    h.a_pos h.a_lt_half h.b_pos h.b_lt_half
    (by nlinarith only [hspans.1]) hspans.2 hwidths.1.1 hwidths.1.2

/-- Two distinct obtuse upper normals cannot occur in actual supported source data. -/
theorem same_obtuse_false (h : UpperSupportedSource d reversed P)
    (hφ : Real.pi / 2 < d.φ) (hψ : Real.pi / 2 < d.ψ) (hne : d.φ ≠ d.ψ) : False := by
  have hπ := Real.pi_pos
  have hspans := h.same_obtuse_spans hφ hψ hne
  have hwidths := h.source_widths
  exact TwoSideFaces.same_obtuse_false
    (Real.cos d.φ) (Real.sin d.φ) (Real.cos d.ψ) (Real.sin d.ψ) d.a d.b
    (Real.cos_neg_of_pi_div_two_lt_of_lt hφ (by linarith [h.phi_lt_pi]))
    (Real.sin_pos_of_mem_Ioo ⟨h.phi_pos, h.phi_lt_pi⟩)
    (Real.cos_neg_of_pi_div_two_lt_of_lt hψ (by linarith [h.psi_lt_pi]))
    (Real.sin_pos_of_mem_Ioo ⟨h.psi_pos, h.psi_lt_pi⟩)
    (Real.cos_sq_add_sin_sq d.φ) (Real.cos_sq_add_sin_sq d.ψ)
    h.a_pos h.a_lt_half h.b_pos h.b_lt_half
    (by nlinarith only [hspans.1]) hspans.2 hwidths.2.1 hwidths.2.2

end UpperSupportedSource

end Puzzling139335.SourceFaceBridge
