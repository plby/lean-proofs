import Wikipedia.NoExoticSixSphere.UnitSurgeryCoordinates

/-!
# The exact rounded-end overlap maps agree in the canonical surgery quotient

Unit-radius normalization makes the left radial exchange use precisely the
same `sqrt (1 + u)` radius. On the right the rounded graph is the original
height-zero tube. Thus both identifications are the existing surgery
quotient identifications, not a new relation chosen on the trace boundary.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace SmoothCornerRounding
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def leftOverlap (p : boundaryCollarParameters A) (hu : p.val.2.2 < -2 * (bump A).rOut) :
    FramedSurgery.Overlap (Vector 4) (Vector 3) :=
  (p.val.1, ⟨collarOriginalVector A p, collarOriginalVector_ne_zero A p, by
    rw [norm_collarOriginalVector]
    have hs : (Real.sqrt (1 + p.val.2.2)) ^ 2 = 1 + p.val.2.2 :=
      Real.sq_sqrt (by linarith [collar_parameter_gt_neg_one A p])
    nlinarith [(bump A).rOut_pos, Real.sqrt_nonneg (1 + p.val.2.2)]⟩)

theorem oldOverlap_leftOverlap (p : boundaryCollarParameters A)
    (hu : p.val.2.2 < -2 * (bump A).rOut) :
    FramedSurgery.oldOverlap (E := Vector 4) (face A hR) (leftOverlap A p hu) =
      collarPoint A hR p := Subtype.ext rfl

omit [T2Space M] in
theorem newOverlap_leftOverlap (p : boundaryCollarParameters A)
    (hu : p.val.2.2 < -2 * (bump A).rOut) :
    FramedSurgery.newOverlap (E := Vector 4) (F := Vector 3) 3 2 (leftOverlap A p hu) =
      handlePoint A (leftCollarToHandle A p hu) := by
  apply Prod.ext
  · apply Subtype.ext
    change ‖collarOriginalVector A p‖ • p.val.1.val =
      RadialHeightCoordinates.point (p.val.1, p.val.2.2)
    rw [norm_collarOriginalVector]
    rfl
  · apply Subtype.ext
    change ‖collarOriginalVector A p‖⁻¹ • collarOriginalVector A p = p.val.2.1.val
    rw [norm_collarOriginalVector, collarOriginalVector, smul_smul,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by linarith [collar_parameter_gt_neg_one A p])),
      one_smul]

theorem left_overlap_agreement (p : boundaryCollarParameters A)
    (hu : p.val.2.2 < -2 * (bump A).rOut) :
    collarMap A hR p = handleMap A hR (leftCollarToHandle A p hu) := by
  have h := FramedSurgery.overlap_identification (E := Vector 4) (F := Vector 3)
    (face A hR) 2 (leftOverlap A p hu)
  rw [oldOverlap_leftOverlap A hR p hu, newOverlap_leftOverlap A p hu] at h
  exact h

theorem right_overlap_points (p : boundaryCollarParameters A)
    (hu : 2 * (bump A).rOut < p.val.2.2) :
    collarPoint A hR p = exteriorPoint A hR (rightCollarToExterior A p hu) := by
  apply Subtype.ext
  change A.tube (p.val.1, Real.sqrt (1 + p.val.2.2) • p.val.2.1.val) =
    A.tube (p.val.1, graphRadius (bump A) (UnroundedTrace.handleRadius A) p.val.2.2 • p.val.2.1.val)
  rw [graphRadius, handleRadius_eq_one A hR,
    graphRadial_of_right (bump A) (by linarith [(bump A).rOut_pos])]
  simp only [one_pow, sub_neg_eq_add]

theorem right_overlap_agreement (p : boundaryCollarParameters A)
    (hu : 2 * (bump A).rOut < p.val.2.2) :
    collarMap A hR p = exteriorMap A hR (rightCollarToExterior A p hu) :=
  congrArg (FramedSurgery.oldMap (E := Vector 4) (face A hR) 2) (right_overlap_points A hR p hu)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
