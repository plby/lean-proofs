import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceBoundaryCoordinates
import Wikipedia.NoExoticSixSphere.OpenOverlapCoordinates

/-!

# Smooth overlap maps on the actual seven-dimensional trace boundary

The regular-zero smooth-map criteria reduce every boundary overlap to the
already proved coordinate change on the underlying trace overlap. No new
identification of ambient points is introduced.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem contMDiff_boundaryCollarToCylinder : letI := boundaryPieceAtlas A .collar;
    letI := boundaryPieceAtlas A .cylinder;
    ContMDiff (𝓡 7) (𝓡 7) ∞
      (OpenOverlap.map (boundaryPieceDomain A .collar) (boundaryPieceDomain A .cylinder)) := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .cylinder
  apply (contMDiff_cylinderBoundary_iff_coordinates A _).mpr
  exact OpenOverlap.contMDiff_coordinates
    (boundaryPieceDomain A .collar) (boundaryPieceDomain A .cylinder)
    (collarBoundaryCoordinates A) (cylinderBoundaryCoordinates A)
    A.tubeHeightCoordinates (contMDiff_collarBoundaryCoordinates A)
    (fun p ↦ collarParameters_subset_source A
      ((collarHomeomorph A).symm (boundaryTracePoint A .collar p.val)).property)
    (fun p ↦ cylinder_collar_coordinate_eq A
      (boundaryTracePoint A .cylinder (OpenOverlap.map _ _ p))
      (boundaryTracePoint A .collar p.val) rfl)

theorem contMDiff_boundaryCylinderToCollar : letI := boundaryPieceAtlas A .cylinder;
    letI := boundaryPieceAtlas A .collar;
    ContMDiff (𝓡 7) (𝓡 7) ∞
      (OpenOverlap.map (boundaryPieceDomain A .cylinder) (boundaryPieceDomain A .collar)) := by
  let := boundaryPieceAtlas A .cylinder
  let := boundaryPieceAtlas A .collar
  apply (contMDiff_collarBoundary_iff_coordinates A _).mpr
  refine OpenOverlap.contMDiff_coordinates
    (boundaryPieceDomain A .cylinder) (boundaryPieceDomain A .collar)
    (cylinderBoundaryCoordinates A) (collarBoundaryCoordinates A)
    A.tubeHeightCoordinates.symm (contMDiff_cylinderBoundaryCoordinates A) ?_ ?_
  · intro p
    let q := boundaryTracePoint A .collar (OpenOverlap.map _ _ p)
    change (unchangedCylinderHomeomorph A (boundaryTracePoint A .cylinder p.val)).val.val ∈
      A.tubeHeightCoordinates.target
    rw [cylinder_collar_coordinate_eq A (boundaryTracePoint A .cylinder p.val) q rfl]
    exact A.tubeHeightCoordinates.map_source
      (collarParameters_subset_source A ((collarHomeomorph A).symm q).property)
  · intro p
    exact collar_cylinder_coordinate_eq A (boundaryTracePoint A .cylinder p.val)
      (boundaryTracePoint A .collar (OpenOverlap.map _ _ p)) rfl

theorem contMDiff_boundaryHandleToCollar : letI := boundaryPieceAtlas A .handle;
    letI := boundaryPieceAtlas A .collar;
    ContMDiff (𝓡 7) (𝓡 7) ∞
      (OpenOverlap.map (boundaryPieceDomain A .handle) (boundaryPieceDomain A .collar)) := by
  let := boundaryPieceAtlas A .handle
  let := boundaryPieceAtlas A .collar
  apply (contMDiff_collarBoundary_iff_coordinates A _).mpr
  exact OpenOverlap.contMDiff_coordinates
    (boundaryPieceDomain A .handle) (boundaryPieceDomain A .collar)
    (handleBoundaryCoordinates A) (collarBoundaryCoordinates A)
    (handleCollarChange A) (contMDiff_handleBoundaryCoordinates A)
    (fun p ↦ handleCollarChange_source A (boundaryTracePoint A .handle p.val)
      (boundaryTracePoint A .collar (OpenOverlap.map _ _ p)) rfl)
    (fun p ↦ (handleCollarChange_apply A (boundaryTracePoint A .handle p.val)
      (boundaryTracePoint A .collar (OpenOverlap.map _ _ p)) rfl).symm)

theorem contMDiff_boundaryCollarToHandle : letI := boundaryPieceAtlas A .collar;
    letI := boundaryPieceAtlas A .handle;
    ContMDiff (𝓡 7) (𝓡 7) ∞
      (OpenOverlap.map (boundaryPieceDomain A .collar) (boundaryPieceDomain A .handle)) := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .handle
  apply (contMDiff_handleBoundary_iff_coordinates A _).mpr
  exact OpenOverlap.contMDiff_coordinates
    (boundaryPieceDomain A .collar) (boundaryPieceDomain A .handle)
    (collarBoundaryCoordinates A) (handleBoundaryCoordinates A)
    (handleCollarChange A).symm (contMDiff_collarBoundaryCoordinates A)
    (fun p ↦ handleCollarChange_target A
      (boundaryTracePoint A .handle (OpenOverlap.map _ _ p))
      (boundaryTracePoint A .collar p.val) rfl)
    (fun p ↦ (handleCollarChange_symm_apply A
      (boundaryTracePoint A .handle (OpenOverlap.map _ _ p))
      (boundaryTracePoint A .collar p.val) rfl).symm)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

