import StackExchange.Puzzling139335.SourceFaceBridge.GlideBounds
import StackExchange.Puzzling139335.SourceFaceBridge.Frontier
import StackExchange.Puzzling139335.JordanTransport
import StackExchange.Puzzling139335.SegmentCrossing

/-!
# Actual supported glide copies cannot have disjoint Jordan interiors

The determinant identities below use the original placement coordinates.
Their denominator is the negative of the positive sine difference, so the
Cramer parameters are `-G / sin (α - β)` and `-F / sin (α - β)`.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

noncomputable section

namespace FaceData

/-- The determinant in the original, unreflected placement coordinates. -/
theorem glide_base_det (d : FaceData) :
    SegmentCrossing.det
      (d.right (point 1 0) - d.right (point 0 0))
      (d.leftGlide (point 1 0) - d.leftGlide (point 0 0)) =
      -Real.sin (d.α - d.β) := by
  simp [SegmentCrossing.det, right, leftGlide, normal₁, normal₂,
    tangent₁, tangent₂, point, Real.sin_sub]

/-- The numerator for the parameter along the right copy's base is `G`. -/
theorem glide_cramer_right_numerator (d : FaceData) :
    SegmentCrossing.det
      (d.leftGlide (point 0 0) - d.right (point 0 0))
      (d.leftGlide (point 1 0) - d.leftGlide (point 0 0)) =
      GlideCrossing.secondDeterminant d.α d.β (d.M₁ 0) (d.M₁ 1) (d.M₂ 1) := by
  calc
    _ = Real.sin d.β * (1 - d.normal₁ d.M₁ - d.normal₂ d.M₂) +
        Real.cos d.β * (d.tangent₁ d.M₁ - d.tangent₂ d.M₂) := by
      simp [SegmentCrossing.det, right, leftGlide, normal₁, normal₂,
        tangent₁, tangent₂, point]
      ring
    _ = _ := by
      dsimp [normal₁, normal₂, tangent₁, tangent₂, GlideCrossing.secondDeterminant]
      rw [Real.sin_sub, Real.cos_sub]
      exact GlideCrossing.secondDet_identity (Real.cos d.α) (Real.sin d.α)
        (Real.cos d.β) (Real.sin d.β) (d.M₁ 0) (d.M₁ 1) (d.M₂ 0) (d.M₂ 1)
        (Real.cos_sq_add_sin_sq d.β)

/-- The numerator for the parameter along the left copy's base is `F`. -/
theorem glide_cramer_left_numerator (d : FaceData) :
    SegmentCrossing.det
      (d.leftGlide (point 0 0) - d.right (point 0 0))
      (d.right (point 1 0) - d.right (point 0 0)) =
      GlideCrossing.firstDeterminant d.α d.β (d.M₁ 1) (d.M₂ 0) (d.M₂ 1) := by
  calc
    _ = Real.sin d.α * (1 - d.normal₁ d.M₁ - d.normal₂ d.M₂) +
        Real.cos d.α * (d.tangent₁ d.M₁ - d.tangent₂ d.M₂) := by
      simp [SegmentCrossing.det, right, leftGlide, normal₁, normal₂,
        tangent₁, tangent₂, point]
      ring
    _ = _ := by
      dsimp [normal₁, normal₂, tangent₁, tangent₂, GlideCrossing.firstDeterminant]
      rw [Real.sin_sub, Real.cos_sub]
      exact GlideCrossing.firstDet_identity (Real.cos d.α) (Real.sin d.α)
        (Real.cos d.β) (Real.sin d.β) (d.M₁ 0) (d.M₁ 1) (d.M₂ 0) (d.M₂ 1)
        (Real.cos_sq_add_sin_sq d.α)

end FaceData

private theorem negative_div_mem_Ioo {F D : ℝ} (hD : 0 < D)
    (hF : F ∈ Ioo (-D) 0) : F / (-D) ∈ Ioo (0 : ℝ) 1 := by
  have hneg : 0 < -F := by linarith only [hF.2]
  have hratio : (-F) / D ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos hneg hD, (div_lt_iff₀ hD).2 ?_⟩
    linarith only [hF.1]
  simpa only [div_neg, neg_div] using hratio

namespace SupportedSource

/-- The normalized glide configuration is impossible for disjoint Jordan
interiors. The input interface is an actual nontrivial intersection of the
two image sets, and the crossed segments lie in their actual frontiers. -/
theorem glide_not_disjoint_interiors {d : FaceData} {P : Set Plane}
    (h : SupportedSource d true P) (hP : IsJordanRegion P) (hβα : d.β < d.α)
    (hcommon : ((d.right '' P) ∩ (d.leftGlide '' P)).Nontrivial) :
    ¬ Disjoint (interior (d.right '' P)) (interior (d.leftGlide '' P)) := by
  obtain ⟨hF, hG⟩ := h.glide_crossing_signs hβα hcommon
  have hD : 0 < Real.sin (d.α - d.β) :=
    (GlideCrossing.strictAngleDifference d.α d.β
      h.beta_pos hβα h.alpha_lt_half_pi).1
  have hR : IsJordanRegion (d.right '' P) :=
    hP.image_homeomorph d.rightIsometry.toHomeomorph
  have hT : IsJordanRegion (d.leftGlide '' P) :=
    hP.image_homeomorph d.leftGlideIsometry.toHomeomorph
  refine SegmentCrossing.not_disjoint_interiors_of_cramer hR hT
    h.right_base_frontier h.leftGlide_base_frontier ?_ ?_ ?_
  · rw [d.glide_base_det]
    exact neg_ne_zero.mpr hD.ne'
  · rw [d.glide_cramer_right_numerator, d.glide_base_det]
    exact negative_div_mem_Ioo hD hG
  · rw [d.glide_cramer_left_numerator, d.glide_base_det]
    exact negative_div_mem_Ioo hD hF

end SupportedSource

end

end Puzzling139335.SourceFaceBridge
