import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceGlobalOutwardNormal
import Wikipedia.NoExoticSixSphere.CoorientedHypersurfaceLift

/-!

# The global unit normal is outward in every native superlevel piece

Each unique preimage of the ambient normal under the actual piece immersion
has negative defining differential. The sign is checked after projection
and normalization, not only on the initial transverse direction.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel LowRoundedHandleCorner

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem outwardNormal_cylinder_unitNormal (p : boundaryPieceDomain A .cylinder) :
    outwardNormal A p.val = CoorientedHypersurfaceNormal.unitNormal
      ((LowHeightCylinder.heightCylinderDerivative d e) (cylinderBoundaryCoordinates A p))
      (cylinderBoundaryLevelDerivative A p) (cylinderOutwardDirection A p) := by
  rw [outwardNormal_on_piece]
  simp only [pieceOutwardNormal, boundaryNormalProjection_eq, boundaryTangent_cylinder]
  rfl

theorem outwardNormal_handle_unitNormal (p : boundaryPieceDomain A .handle) :
    outwardNormal A p.val = CoorientedHypersurfaceNormal.unitNormal
      (fderiv ℝ A.map (handleBoundaryCoordinates A p))
      (fderiv ℝ (LowHandleSuperlevel.level (UnroundedTrace.handleRadius A))
        (handleBoundaryCoordinates A p)) (handleOutwardDirection A p) := by
  rw [outwardNormal_on_piece]
  simp only [pieceOutwardNormal, boundaryNormalProjection_eq, boundaryTangent_handle]
  rfl

theorem outwardNormal_collar_unitNormal (p : boundaryPieceDomain A .collar) :
    outwardNormal A p.val = CoorientedHypersurfaceNormal.unitNormal
      (A.collarSheetDerivative (collarBoundaryCoordinates A p))
      (collarBoundaryLevelDerivative A p) (collarOutwardDirection A p) := by
  rw [outwardNormal_on_piece]
  exact normalized_collarVector A p (collarOutwardDirection A p)

theorem cylinder_outward_lift_negative (p : boundaryPieceDomain A .cylinder)
    (v : Vector 7 × ℝ)
    (hv : LowHeightCylinder.heightCylinderDerivative d e (cylinderBoundaryCoordinates A p) v =
      outwardNormal A p.val) :
    cylinderBoundaryLevelDerivative A p v < 0 := by
  rw [outwardNormal_cylinder_unitNormal] at hv
  exact CoorientedHypersurfaceNormal.level_unitNormal_lift_negative _ _
    ((LowHeightCylinder.injective_heightCylinderDerivative d e) _) _ v
    (cylinderOutwardDirection_negative A p) hv

theorem handle_outward_lift_negative (p : boundaryPieceDomain A .handle)
    (v : Vector (d + 1) × Vector (7 - d))
    (hv : fderiv ℝ A.map (handleBoundaryCoordinates A p) v = outwardNormal A p.val) :
    fderiv ℝ (LowHandleSuperlevel.level (UnroundedTrace.handleRadius A))
      (handleBoundaryCoordinates A p) v < 0 := by
  rw [outwardNormal_handle_unitNormal] at hv
  let q := unchangedHandleHomeomorph A (boundaryTracePoint A .handle p)
  have hi : Injective (fderiv ℝ A.map (handleBoundaryCoordinates A p)) :=
    A.immersive q.val.val.1 (ball_subset_closedBall q.property.1) q.val.val.2
      (handleSuperlevel_vector_mem A q.val)
  exact CoorientedHypersurfaceNormal.level_unitNormal_lift_negative _ _ hi _ v
    (handleOutwardDirection_negative A p) hv

theorem collar_outward_lift_negative (p : boundaryPieceDomain A .collar)
    (v : (Vector d × Vector (7 - d)) × ℝ)
    (hv : A.collarSheetDerivative (collarBoundaryCoordinates A p) v = outwardNormal A p.val) :
    collarBoundaryLevelDerivative A p v < 0 := by
  rw [outwardNormal_collar_unitNormal] at hv
  have hi := A.injective_collarSheetDerivative (collarParameters_subset_source A
    ((collarHomeomorph A).symm (boundaryTracePoint A .collar p)).property)
  exact CoorientedHypersurfaceNormal.level_unitNormal_lift_negative _ _ hi _ v
    (collarOutwardDirection_negative A p) hv

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
