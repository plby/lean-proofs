import StackExchange.Puzzling139335.SourceFaceBridge.ProperModel
import StackExchange.Puzzling139335.GlideCrossing

/-!
# Geometric source data imply the glide determinant bounds

The finite model supplies the strip-width arm caps, the face-height bounds,
and the center-coordinate bounds required by the analytic crossing theorem.
-/

namespace Puzzling139335.SourceFaceBridge

noncomputable section

private theorem cap_of_circle_width (x y a : ℝ)
    (hx : 0 < x) (hy : 0 ≤ y) (hcircle : x ^ 2 + y ^ 2 = 1)
    (hwidth : y + x * a ≤ 1) : a ≤ x / (1 + y) := by
  have hden : 0 < 1 + y := by linarith
  have hmul := mul_le_mul_of_nonneg_right hwidth hden.le
  have hscale : x * (a * (1 + y)) ≤ x * x := by
    nlinarith only [hmul, hcircle]
  exact (le_div_iff₀ hden).2 (le_of_mul_le_mul_left hscale hx)

/-- Three arm caps follow from the two source strip systems. -/
theorem model_arm_caps {p : ProperRotation.Data} (h : ProperRotation.Model p) :
    p.a ≤ min (1 / 2) (p.d / (1 + p.q)) ∧
      p.b ≤ min (p.q / (1 + p.d)) (p.c / (1 + p.s)) := by
  have haWidth : p.q + p.d * p.a ≤ 1 := by
    nlinarith only [h.left_top.tangent2_upper, h.base_right.tangent2_lower]
  have hbNormal : p.d + p.q * p.b ≤ 1 := by
    nlinarith only [h.origin.normal2_lower, h.right_top.normal2_upper]
  have hbTangent : p.s + p.c * p.b ≤ 1 := by
    nlinarith only [h.origin.tangent1_upper, h.right_top.tangent1_lower]
  have ha := cap_of_circle_width p.d p.q p.a h.d_pos h.q_pos.le h.dq_circle haWidth
  have hb₁ := cap_of_circle_width p.q p.d p.b h.q_pos h.d_pos.le
    (by nlinarith only [h.dq_circle]) hbNormal
  have hb₂ := cap_of_circle_width p.c p.s p.b h.c_pos h.s_pos.le
    h.cs_circle hbTangent
  exact ⟨le_min h.a_lt_half.le ha, le_min hb₁ hb₂⟩

/-- The needed upper bounds on both face centers come from endpoint containment. -/
theorem model_center_bounds {p : ProperRotation.Data} (h : ProperRotation.Model p) :
    p.x1 ≤ 1 - p.s * p.bGap ∧
      p.y1 ≤ 1 / 2 - p.c * p.bGap ∧
      p.x2 ≤ 1 ∧
      p.y2 ≤ 1 / 2 - p.d * p.aGap := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [h.face1_plus.x_le_one]
  · nlinarith only [h.face1_plus.y_le_half]
  · nlinarith only [h.face2_minus.x_le_one, h.face2_plus.x_le_one]
  · nlinarith only [h.face2_plus.y_le_half]

/-- The first determinant at a common point, including equal placement angles. -/
theorem glide_common_first_identity {d : FaceData} {r t : Plane}
    (heq : d.right r = d.leftGlide t) :
    GlideCrossing.firstDeterminant d.α d.β (d.M₁ 1) (d.M₂ 0) (d.M₂ 1) +
      Real.sin (d.α - d.β) * t 0 + Real.cos (d.α - d.β) * t 1 + r 1 = 0 := by
  have hx := congrArg (fun q : Plane => q 0) heq
  have hy := congrArg (fun q : Plane => q 1) heq
  change 1 + d.normal₁ r - d.normal₁ d.M₁ = d.normal₂ d.M₂ - d.normal₂ t at hx
  change 1 / 2 + d.tangent₁ r - d.tangent₁ d.M₁ =
    1 / 2 + d.tangent₂ t - d.tangent₂ d.M₂ at hy
  dsimp [FaceData.normal₁, FaceData.normal₂, FaceData.tangent₁, FaceData.tangent₂] at hx hy
  dsimp [GlideCrossing.firstDeterminant]
  rw [Real.sin_sub, Real.cos_sub]
  linear_combination Real.sin d.α * hx - Real.cos d.α * hy -
    (r 1 - d.M₁ 1) * Real.cos_sq_add_sin_sq d.α

private theorem glide_common_second_identity {d : FaceData} {r t : Plane}
    (heq : d.right r = d.leftGlide t) :
    GlideCrossing.secondDeterminant d.α d.β (d.M₁ 0) (d.M₁ 1) (d.M₂ 1) +
      Real.sin (d.α - d.β) * r 0 + Real.cos (d.α - d.β) * r 1 + t 1 = 0 := by
  have hx := congrArg (fun q : Plane => q 0) heq
  have hy := congrArg (fun q : Plane => q 1) heq
  change 1 + d.normal₁ r - d.normal₁ d.M₁ = d.normal₂ d.M₂ - d.normal₂ t at hx
  change 1 / 2 + d.tangent₁ r - d.tangent₁ d.M₁ =
    1 / 2 + d.tangent₂ t - d.tangent₂ d.M₂ at hy
  dsimp [FaceData.normal₁, FaceData.normal₂, FaceData.tangent₁, FaceData.tangent₂] at hx hy
  dsimp [GlideCrossing.secondDeterminant]
  rw [Real.sin_sub, Real.cos_sub]
  linear_combination Real.sin d.β * hx - Real.cos d.β * hy -
    (t 1 - d.M₂ 1) * Real.cos_sq_add_sin_sq d.β

namespace SupportedSource

/-- The analytic lower signs require only the concrete source geometry.
They are independent of the left-placement parity. -/
theorem glide_lower_bounds {d : FaceData} {reversed : Bool} {P : Set Plane}
    (h : SupportedSource d reversed P) (hβα : d.β < d.α) :
    -Real.sin (d.α - d.β) <
        GlideCrossing.firstDeterminant d.α d.β (d.M₁ 1) (d.M₂ 0) (d.M₂ 1) ∧
      -Real.sin (d.α - d.β) <
        GlideCrossing.secondDeterminant d.α d.β (d.M₁ 0) (d.M₁ 1) (d.M₂ 1) := by
  have hm := h.toProperModel
  have hheight₁ := hm.first_height
  have hheight₂ := hm.second_height
  change 2 * (1 / 2 - d.b) * Real.cos d.α ≤ 1 / 2 - d.a at hheight₁
  change 2 * (1 / 2 - d.a) * Real.cos d.β ≤ 1 / 2 - d.b at hheight₂
  have hcaps := model_arm_caps hm
  change d.a ≤ min (1 / 2) (Real.cos d.β / (1 + Real.sin d.β)) ∧
    d.b ≤ min (Real.sin d.β / (1 + Real.cos d.β))
      (Real.cos d.α / (1 + Real.sin d.α)) at hcaps
  have hcenters := model_center_bounds hm
  simp only [FaceData.scalarData_x1, FaceData.scalarData_y1,
    FaceData.scalarData_x2, FaceData.scalarData_y2] at hcenters
  change d.M₁ 0 ≤ 1 - Real.sin d.α * (1 / 2 - d.b) ∧
    d.M₁ 1 ≤ 1 / 2 - Real.cos d.α * (1 / 2 - d.b) ∧
    d.M₂ 0 ≤ 1 ∧
    d.M₂ 1 ≤ 1 / 2 - Real.cos d.β * (1 / 2 - d.a) at hcenters
  exact GlideCrossing.sourceBounds_lower d.α d.β d.a d.b
    (d.M₁ 0) (d.M₁ 1) (d.M₂ 0) (d.M₂ 1)
    h.beta_pos hβα h.alpha_lt_half_pi h.b_lt_half
    (by nlinarith only [hheight₁]) (by nlinarith only [hheight₂])
    hcaps.1 hcaps.2 hcenters.1 hcenters.2.1 hcenters.2.2.1 hcenters.2.2.2

/-- A nonnegative first determinant confines every common point to the
image of the left copy's intrinsic origin. -/
theorem glide_common_eq_left_corner {d : FaceData} {P : Set Plane}
    (h : SupportedSource d true P) (hβα : d.β < d.α)
    (hF : 0 ≤ GlideCrossing.firstDeterminant d.α d.β
      (d.M₁ 1) (d.M₂ 0) (d.M₂ 1))
    {z : Plane} (hz : z ∈ (d.right '' P) ∩ (d.leftGlide '' P)) :
    z = d.leftGlide (point 0 0) := by
  rcases hz.1 with ⟨r, hr, hrz⟩
  rcases hz.2 with ⟨t, ht, htz⟩
  have heq : d.right r = d.leftGlide t := hrz.trans htz.symm
  have hidentity := glide_common_first_identity heq
  have hrbox := h.source_subset hr
  have htbox := h.source_subset ht
  obtain ⟨hD, hK⟩ := GlideCrossing.strictAngleDifference d.α d.β
    h.beta_pos hβα h.alpha_lt_half_pi
  have hline : GlideCrossing.firstDeterminant d.α d.β
      (d.M₁ 1) (d.M₂ 0) (d.M₂ 1) +
      Real.sin (d.α - d.β) * t 0 + Real.cos (d.α - d.β) * t 1 ≤ 0 := by
    linarith only [hidentity, hrbox.2.1]
  obtain ⟨_, hx, hy⟩ := GlideCrossing.corner_intersection_coordinates
    (GlideCrossing.firstDeterminant d.α d.β (d.M₁ 1) (d.M₂ 0) (d.M₂ 1))
    (Real.sin (d.α - d.β)) (Real.cos (d.α - d.β)) (t 0) (t 1)
    hF hD hK htbox.1.1 htbox.2.1 hline
  have ht0 : t = point 0 0 := point_ext hx hy
  exact htz.symm.trans (congrArg d.leftGlide ht0)

/-- The symmetric coordinate argument for the second determinant. -/
theorem glide_common_eq_right_corner {d : FaceData} {P : Set Plane}
    (h : SupportedSource d true P) (hβα : d.β < d.α)
    (hG : 0 ≤ GlideCrossing.secondDeterminant d.α d.β
      (d.M₁ 0) (d.M₁ 1) (d.M₂ 1))
    {z : Plane} (hz : z ∈ (d.right '' P) ∩ (d.leftGlide '' P)) :
    z = d.right (point 0 0) := by
  rcases hz.1 with ⟨r, hr, hrz⟩
  rcases hz.2 with ⟨t, ht, htz⟩
  have heq : d.right r = d.leftGlide t := hrz.trans htz.symm
  have hidentity := glide_common_second_identity heq
  have hrbox := h.source_subset hr
  have htbox := h.source_subset ht
  obtain ⟨hD, hK⟩ := GlideCrossing.strictAngleDifference d.α d.β
    h.beta_pos hβα h.alpha_lt_half_pi
  have hline : GlideCrossing.secondDeterminant d.α d.β
      (d.M₁ 0) (d.M₁ 1) (d.M₂ 1) +
      Real.sin (d.α - d.β) * r 0 + Real.cos (d.α - d.β) * r 1 ≤ 0 := by
    linarith only [hidentity, htbox.2.1]
  obtain ⟨_, hx, hy⟩ := GlideCrossing.corner_intersection_coordinates
    (GlideCrossing.secondDeterminant d.α d.β (d.M₁ 0) (d.M₁ 1) (d.M₂ 1))
    (Real.sin (d.α - d.β)) (Real.cos (d.α - d.β)) (r 0) (r 1)
    hG hD hK hrbox.1.1 hrbox.2.1 hline
  have hr0 : r = point 0 0 := point_ext hx hy
  exact hrz.symm.trans (congrArg d.right hr0)

/-- Two distinct common points supply the strict upper determinant signs. -/
theorem glide_upper_bounds {d : FaceData} {P : Set Plane}
    (h : SupportedSource d true P) (hβα : d.β < d.α)
    (hcommon : ((d.right '' P) ∩ (d.leftGlide '' P)).Nontrivial) :
    GlideCrossing.firstDeterminant d.α d.β (d.M₁ 1) (d.M₂ 0) (d.M₂ 1) < 0 ∧
      GlideCrossing.secondDeterminant d.α d.β (d.M₁ 0) (d.M₁ 1) (d.M₂ 1) < 0 := by
  rcases hcommon with ⟨z, hz, w, hw, hzw⟩
  constructor
  · by_contra hF
    exact hzw ((h.glide_common_eq_left_corner hβα (le_of_not_gt hF) hz).trans
      (h.glide_common_eq_left_corner hβα (le_of_not_gt hF) hw).symm)
  · by_contra hG
    exact hzw ((h.glide_common_eq_right_corner hβα (le_of_not_gt hG) hz).trans
      (h.glide_common_eq_right_corner hβα (le_of_not_gt hG) hw).symm)

/-- Concrete supported geometry and a nontrivial common interface give all
four strict determinant inequalities for a proper base crossing. -/
theorem glide_crossing_signs {d : FaceData} {P : Set Plane}
    (h : SupportedSource d true P) (hβα : d.β < d.α)
    (hcommon : ((d.right '' P) ∩ (d.leftGlide '' P)).Nontrivial) :
    GlideCrossing.firstDeterminant d.α d.β (d.M₁ 1) (d.M₂ 0) (d.M₂ 1) ∈
        Set.Ioo (-Real.sin (d.α - d.β)) 0 ∧
      GlideCrossing.secondDeterminant d.α d.β (d.M₁ 0) (d.M₁ 1) (d.M₂ 1) ∈
        Set.Ioo (-Real.sin (d.α - d.β)) 0 := by
  obtain ⟨hFlower, hGlower⟩ := h.glide_lower_bounds hβα
  obtain ⟨hFupper, hGupper⟩ := h.glide_upper_bounds hβα hcommon
  exact ⟨⟨hFlower, hFupper⟩, ⟨hGlower, hGupper⟩⟩

end SupportedSource

end

end Puzzling139335.SourceFaceBridge
