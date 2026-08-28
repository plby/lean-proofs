import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryCoordinateInjectivity

/-!
# Canonical surgery identifies only the actual rounded-end overlaps

Equality in the independently defined surgery quotient forces exactly the
handle-side or exterior-side collar inequality. No point in the retained
exterior is identified with a point in the smaller handle piece.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner RoundedTrace
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem exteriorMap_ne_handleMap (m : retainedExterior A) (q : boundaryHandleParameters A) :
    exteriorMap A hR m ≠ handleMap A hR q := by
  intro he
  obtain ⟨z, hz, _⟩ := (FramedSurgery.old_eq_new_iff (E := Vector 4) (face A hR) 3
    (exteriorPoint A hR m) (handlePoint A q)).mp he
  have ht : A.tube (z.1, z.2.val) = m.val := congrArg Subtype.val hz
  have hr : 1 < outerRadius A := by
    rw [← handleRadius_eq_one A hR]
    exact outerRadius_gt_handle A
  exact m.property ⟨(z.1, z.2.val), ⟨mem_univ _,
    mem_closedBall_zero_iff.mpr (z.2.property.2.trans hr).le⟩, ht⟩

theorem collar_exterior_parameter_of_eq (p : boundaryCollarParameters A)
    (m : retainedExterior A) (he : collarMap A hR p = exteriorMap A hR m) :
    2 * (bump A).rOut < p.val.2.2 := by
  have ht : collarPoint A hR p = exteriorPoint A hR m :=
    (FramedSurgery.oldMap_isOpenEmbedding (E := Vector 4) (face A hR) 3).injective he
  have hm : A.tube (p.val.1, collarOriginalVector A p) ∈ retainedExterior A := by
    change (collarPoint A hR p).val ∈ retainedExterior A
    rw [ht]
    exact m.property
  have hn := (tube_mem_retainedExterior_iff A p.val.1
    (collarOriginalVector_mem A hR p)).mp hm
  have hs := outerRadius_sq A
  rw [handleRadius_eq_one A hR] at hs
  nlinarith [collarOriginalVector_norm_sq A p, outerRadius_nonneg A]

theorem collar_handle_parameter_of_eq (p : boundaryCollarParameters A)
    (q : boundaryHandleParameters A) (he : collarMap A hR p = handleMap A hR q) :
    p.val.2.2 < -2 * (bump A).rOut := by
  obtain ⟨z, hz, hy⟩ := (FramedSurgery.old_eq_new_iff (E := Vector 4) (face A hR) 3
    (collarPoint A hR p) (handlePoint A q)).mp he
  have hv : z.2.val ∈ closedBall (0 : Vector 4) A.radius := by
    apply mem_closedBall_zero_iff.mpr
    rw [hR]
    linarith [z.2.property.2]
  have ht := tube_coordinates_eq A hv (collarOriginalVector_mem A hR p)
    (congrArg Subtype.val hz)
  have hn : ‖(handlePoint A q).1.val‖ = ‖z.2.val‖ := by
    rw [← hy, FramedSurgery.newOverlap_fst, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), ClosedHemisphere.unit_norm, mul_one]
  have hx : ‖q.val.1‖ < handleCoreRadius A :=
    mem_ball_zero_iff.mp ((mem_boundaryHandleParameters_iff A q.val).mp q.property)
  have hr : ‖collarOriginalVector A p‖ < handleCoreRadius A := by
    rw [← ht.2, ← hn]
    exact hx
  nlinarith [collarOriginalVector_norm_sq A p, handleCoreRadius_sq A,
    handleCoreRadius_pos A, norm_nonneg (collarOriginalVector A p)]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
