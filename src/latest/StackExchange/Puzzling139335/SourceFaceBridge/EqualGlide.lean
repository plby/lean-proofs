import StackExchange.Puzzling139335.SourceFaceBridge.GlideBounds

/-!
# Equal-angle glide placements have no common point

At equal angles the first common-point identity contains only the two
nonnegative source heights.  The strip widths and face-center bounds make
its determinant strictly positive, giving a contradiction without division
by the sine of the angle difference.
-/

namespace Puzzling139335.SourceFaceBridge

noncomputable section

private theorem equal_cosine_linear_pos (C S : ℝ)
    (hC : 0 < C) (hhalf : C ≤ 1 / 2) (hS : 0 < S)
    (hcircle : C ^ 2 + S ^ 2 = 1) : 0 < 3 * S + C - 3 := by
  have hscale : 0 < C * (3 - 5 * C) := mul_pos hC (by linarith)
  by_contra hgoal
  have hleft : 0 ≤ 3 - C - 3 * S := by linarith
  have hright : 0 ≤ 3 - C + 3 * S := by linarith
  have hsquare := mul_nonneg hleft hright
  nlinarith only [hcircle, hscale, hsquare]

namespace SupportedSource

/-- Equal source angles force the first determinant to be strictly positive.
The bound follows from the concrete strip widths and face endpoints, for
either placement parity. -/
theorem equal_angle_first_pos {d : FaceData} {reversed : Bool} {P : Set Plane}
    (h : SupportedSource d reversed P) (hαβ : d.α = d.β) :
    0 < GlideCrossing.firstDeterminant d.α d.β
      (d.M₁ 1) (d.M₂ 0) (d.M₂ 1) := by
  have hm := h.toProperModel
  have hC : 0 < Real.cos d.α := hm.c_pos
  have hS : 0 < Real.sin d.α := hm.s_pos
  have hprod := hm.cos_product_le
  change 4 * Real.cos d.α * Real.cos d.β ≤ 1 at hprod
  rw [← hαβ] at hprod
  have hhalf := GlideCrossing.smallerCos_le_half
    (Real.cos d.α) (Real.cos d.α) hC.le le_rfl hprod
  have hpositive := equal_cosine_linear_pos (Real.cos d.α) (Real.sin d.α)
    hC hhalf hS (Real.cos_sq_add_sin_sq d.α)
  have ha : d.scalarData.q + d.scalarData.d * d.scalarData.a ≤ 1 := by
    nlinarith only [hm.left_top.tangent2_upper, hm.base_right.tangent2_lower]
  have hb : d.scalarData.s + d.scalarData.c * d.scalarData.b ≤ 1 := by
    nlinarith only [hm.origin.tangent1_upper, hm.right_top.tangent1_lower]
  change Real.sin d.β + Real.cos d.β * d.a ≤ 1 at ha
  change Real.sin d.α + Real.cos d.α * d.b ≤ 1 at hb
  rw [← hαβ] at ha
  have hcenters := model_center_bounds hm
  have hy₁ := hcenters.2.1
  have hy₂ := hcenters.2.2.2
  rw [FaceData.scalarData_y1] at hy₁
  rw [FaceData.scalarData_y2] at hy₂
  change d.M₁ 1 ≤ 1 / 2 - Real.cos d.α * (1 / 2 - d.b) at hy₁
  change d.M₂ 1 ≤ 1 / 2 - Real.cos d.β * (1 / 2 - d.a) at hy₂
  rw [← hαβ] at hy₂
  simp only [GlideCrossing.firstDeterminant, ← hαβ, sub_self,
    Real.sin_zero, Real.cos_zero, zero_mul, one_mul, sub_zero]
  nlinarith only [hpositive, ha, hb, hy₁, hy₂]

/-- The actual two glide images are disjoint when their source angles agree. -/
theorem equal_glide_intersection_eq_empty {d : FaceData} {P : Set Plane}
    (h : SupportedSource d true P) (hαβ : d.α = d.β) :
    (d.right '' P) ∩ (d.leftGlide '' P) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  rcases hz.1 with ⟨r, hr, hrz⟩
  rcases hz.2 with ⟨t, ht, htz⟩
  have heq : d.right r = d.leftGlide t := hrz.trans htz.symm
  have hidentity := glide_common_first_identity heq
  have hpositive := h.equal_angle_first_pos hαβ
  have hrheight := (h.source_subset hr).2.1
  have htheight := (h.source_subset ht).2.1
  simp only [← hαβ, sub_self, Real.sin_zero, Real.cos_zero,
    zero_mul, one_mul, add_zero] at hidentity hpositive
  linarith only [hidentity, hpositive, hrheight, htheight]

end SupportedSource

end

end Puzzling139335.SourceFaceBridge
