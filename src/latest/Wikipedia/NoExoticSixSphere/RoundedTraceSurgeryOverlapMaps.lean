import Wikipedia.NoExoticSixSphere.RoundedTraceExteriorTube

/-!
# Actual overlap maps from the rounded collar to the two surgery pieces

On the left the graph is the old handle collar, with radius `sqrt (1 + u)`.
On the right it is the original tube at height zero. The ambient equalities
below identify the actual maps into the already constructed native boundary.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel RoundedHandleCorner SmoothCornerRounding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem leftCollar_radialPoint_mem_core (p : boundaryCollarParameters A)
    (hu : p.val.2.2 < -2 * (bump A).rOut) :
    RadialHeightCoordinates.point (p.val.1, p.val.2.2) ∈ handleCoreBall A := by
  have hp := (mem_boundaryCollarParameters_iff_interval A p.val).mp p.property
  have hlo : -1 < p.val.2.2 := by
    nlinarith [collarHeight_lt_gap A, sq_nonneg A.innerRadius, hp.1]
  have hx : ‖RadialHeightCoordinates.point (p.val.1, p.val.2.2)‖ ^ 2 = 1 + p.val.2.2 := by
    rw [RadialHeightCoordinates.norm_point, Real.sq_sqrt (by linarith)]
  change _ ∈ ball (0 : Vector 4) (handleCoreRadius A)
  rw [mem_ball, dist_zero_right]
  nlinarith [handleCoreRadius_sq A, handleCoreRadius_pos A,
    norm_nonneg (RadialHeightCoordinates.point (p.val.1, p.val.2.2))]

def leftCollarToHandle (p : boundaryCollarParameters A)
    (hu : p.val.2.2 < -2 * (bump A).rOut) : boundaryHandleParameters A :=
  ⟨(RadialHeightCoordinates.point (p.val.1, p.val.2.2), p.val.2.1),
    (mem_boundaryHandleParameters_iff A _).mpr (leftCollar_radialPoint_mem_core A p hu)⟩

def rightCollarToExterior (p : boundaryCollarParameters A)
    (hu : 2 * (bump A).rOut < p.val.2.2) : retainedExterior A :=
  ⟨A.tube (collarZeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val).1,
    (collar_tube_mem_retainedExterior_iff A p).mpr hu⟩

variable [IsManifold (𝓡 6) ∞ M]

theorem leftCollarToHandle_ambient (p : boundaryCollarParameters A)
    (hu : p.val.2.2 < -2 * (bump A).rOut) :
    letI := boundaryPieceAtlas A .collar; letI := boundaryPieceAtlas A .handle;
    (boundaryCollarDiffeomorph A p).val.val.val =
      (boundaryHandleDiffeomorph A (leftCollarToHandle A p hu)).val.val.val := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .handle
  rw [boundaryCollarDiffeomorph_ambient, boundaryHandleDiffeomorph_ambient]
  have hp := (mem_boundaryCollarParameters_iff_interval A p.val).mp p.property
  have hleft : p.val.2.2 ≤ -(bump A).rOut := by linarith [(bump A).rOut_pos]
  have he : collarZeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val =
      ((p.val.1, UnroundedTrace.handleRadius A • p.val.2.1.val), p.val.2.2) := by
    dsimp only [collarZeroPoint, zeroPoint]
    rw [graphRadius_of_left (bump A) (UnroundedTrace.handleRadius_pos A) hleft,
      graphHeight_of_left (bump A) hleft]
  rw [he]
  have hv : UnroundedTrace.handleRadius A • p.val.2.1.val ∈
      closedBall (0 : Vector 3) A.radius := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (UnroundedTrace.handleRadius_pos A), ClosedHemisphere.unit_norm, mul_one]
    exact (UnroundedTrace.handleRadius_lt A).le
  exact (A.map_radialPoint_eq_sheet p.val.1 hv
    (by linarith [collarHeight_lt_gap A, hp.1])
    (by linarith [(bump A).rOut_pos])).symm

theorem rightCollarToExterior_ambient (p : boundaryCollarParameters A)
    (hu : 2 * (bump A).rOut < p.val.2.2) :
    letI := boundaryPieceAtlas A .collar; letI := boundaryPieceAtlas A .cylinder;
    (boundaryCollarDiffeomorph A p).val.val.val =
      (exteriorBoundaryDiffeomorph A (rightCollarToExterior A p hu)).val.val.val.val := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .cylinder
  rw [boundaryCollarDiffeomorph_ambient, exteriorBoundaryDiffeomorph_ambient,
    A.collarSheet_apply]
  change e.heightCylinder
    (A.tube (collarZeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val).1,
      graphHeight (bump A) p.val.2.2) = _
  rw [graphHeight_of_right (bump A) (by linarith [(bump A).rOut_pos])]
  rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
