import Wikipedia.NoExoticSixSphere.RoundedTraceSurgeryOverlapMaps

/-!
# Exact overlaps of the three pieces of the complementary boundary end

In the actual rounded-collar parameter, the handle overlap is exactly
`u < -2 rOut` and the retained-original overlap is exactly `2 rOut < u`.
Together with the actual ambient overlap maps, these identify both the
domains and maps of the surgery gluing data.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel RoundedHandleCorner SmoothCornerRounding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem boundaryCollar_mem_handle_iff (p : boundaryCollarParameters A) :
    letI := boundaryPieceAtlas A .collar;
    (boundaryCollarDiffeomorph A p).val.val ∈ handleOnlyPart A ↔
      p.val.2.2 < -2 * (bump A).rOut := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .handle
  constructor
  · intro hp
    let q : handleOnlyPart A := ⟨(boundaryCollarDiffeomorph A p).val.val, hp⟩
    have he := handle_collar_coordinate_eq A q
      (boundaryTracePoint A .collar (boundaryCollarDiffeomorph A p)) rfl
    have ht := congrArg Prod.snd he
    change ‖(unchangedHandleHomeomorph A q).val.val.1‖ ^ 2 - 1 =
      (collarBoundaryCoordinates A (boundaryCollarDiffeomorph A p)).2 at ht
    rw [boundaryCollarDiffeomorph_coordinates] at ht
    change ‖(unchangedHandleHomeomorph A q).val.val.1‖ ^ 2 - 1 =
      graphHeight (bump A) p.val.2.2 at ht
    have hx := (mem_unchangedHandleWindow_iff A (unchangedHandleHomeomorph A q).val).mp
      (unchangedHandleHomeomorph A q).property
    have hn : ‖(unchangedHandleHomeomorph A q).val.val.1‖ < handleCoreRadius A := by
      simpa only [mem_ball, dist_zero_right] using hx
    apply (graphHeight_lt_neg_twice_outer_iff (bump A) p.val.2.2).mp
    rw [← ht]
    nlinarith [handleCoreRadius_sq A, handleCoreRadius_pos A,
      norm_nonneg (unchangedHandleHomeomorph A q).val.val.1]
  · intro hu
    have he : (boundaryCollarDiffeomorph A p).val.val =
        (boundaryHandleDiffeomorph A (leftCollarToHandle A p hu)).val.val :=
      Subtype.ext (leftCollarToHandle_ambient A p hu)
    rw [he]
    exact (boundaryHandleDiffeomorph A (leftCollarToHandle A p hu)).property

theorem boundaryCollar_mem_cylinder_iff (p : boundaryCollarParameters A) :
    letI := boundaryPieceAtlas A .collar;
    (boundaryCollarDiffeomorph A p).val.val ∈ cylinderOnlyPart A ↔
      2 * (bump A).rOut < p.val.2.2 := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .cylinder
  constructor
  · intro hp
    let q : boundaryPieceDomain A .cylinder := ⟨(boundaryCollarDiffeomorph A p).val, hp⟩
    let q' : bottomCylinderBoundaryPart A :=
      ⟨q, collarBoundary_mem_other A (boundaryCollarDiffeomorph A p)⟩
    have he := cylinder_collar_coordinate_eq A (boundaryTracePoint A .cylinder q)
      (boundaryTracePoint A .collar (boundaryCollarDiffeomorph A p)) rfl
    have hm := congrArg Prod.fst he
    change (cylinderBoundaryCoordinates A q).1 =
      A.tube (collarBoundaryCoordinates A (boundaryCollarDiffeomorph A p)).1 at hm
    rw [boundaryCollarDiffeomorph_coordinates] at hm
    have hx : (cylinderBoundaryCoordinates A q).1 ∈ retainedExterior A :=
      (bottomBoundaryOriginalPoint A q').property
    rw [hm] at hx
    exact (collar_tube_mem_retainedExterior_iff A p).mp hx
  · intro hu
    have he : (boundaryCollarDiffeomorph A p).val.val =
        (exteriorBoundaryDiffeomorph A (rightCollarToExterior A p hu)).val.val.val :=
      Subtype.ext (rightCollarToExterior_ambient A p hu)
    rw [he]
    exact (exteriorBoundaryDiffeomorph A (rightCollarToExterior A p hu)).val.property

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
