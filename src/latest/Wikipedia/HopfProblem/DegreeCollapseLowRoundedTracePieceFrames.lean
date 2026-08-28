import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceAtlas
import Wikipedia.HopfProblem.DegreeCollapseLowRoundedCollarDifferential

/-!

# Smooth matching normal columns on the actual trace pieces

The original cylinder frame, the retained handle frame, and the rounded
collar frame agree at every common ambient point. In particular, the handle
comparison uses the proved annulus and exact original collar identity.
-/

noncomputable section

open Function Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def pieceNormalFrame : ∀ i : Piece, pieceDomain A i →
    Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1))))
  | .cylinder, p => boundaryFrameOperator d
      (a.orthonormal (unchangedCylinderHomeomorph A p).val.val.1).val
  | .handle, p => A.normalFrame (unchangedHandleHomeomorph A p).val.val
  | .collar, p => collarNormalFrame A p

theorem contMDiff_pieceNormalFrame (i : Piece) : letI := pieceAtlas A i;
    ContMDiff (ProductHalfSpace.model (Vector 7))
      𝓘(ℝ, Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
        Vector (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      (pieceNormalFrame A i) := by
  cases i with
  | cylinder =>
      let := pieceAtlas A .cylinder
      exact (contMDiff_boundaryFrameOperator d a.contMDiff_orthonormal).comp
        (contMDiff_fst.comp (contMDiff_unchangedCylinder_parameters A))
  | handle =>
      let := pieceAtlas A .handle
      intro p
      let q := unchangedHandleHomeomorph A p
      have hs : ContDiffAt ℝ ∞ A.normalFrame q.val.val :=
        A.normalFrame_smooth q.val.val.1 (ball_subset_closedBall q.property.1) q.val.val.2
          (handleSuperlevel_vector_mem A q.val)
      exact hs.contMDiffAt.comp p ((contMDiff_unchangedHandle_parameters A) p)
  | collar => exact contMDiff_collarNormalFrame A

omit [IsManifold (𝓡 7) ∞ M] in
theorem pieceNormalFrame_norm (i : Piece) (p : pieceDomain A i)
    (v : Vector ((e.ambientDimension - 7) + (1 + (d + 1)))) : ‖pieceNormalFrame A i p v‖ = ‖v‖ := by
  cases i with
  | cylinder => exact norm_boundaryFrameOperator d (a.orthonormal _) v
  | handle =>
      let q := unchangedHandleHomeomorph A p
      exact A.normalFrame_norm q.val.val.1 (ball_subset_closedBall q.property.1) q.val.val.2
        (handleSuperlevel_vector_mem A q.val) v
  | collar => exact collarNormalFrame_norm A p v

omit [IsManifold (𝓡 7) ∞ M] in
theorem cylinder_collar_frame_eq (p : cylinderOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) : pieceNormalFrame A .cylinder p = pieceNormalFrame A .collar q := by
  change boundaryFrameOperator d (a.orthonormal (unchangedCylinderHomeomorph A p).val.val.1).val =
    boundaryFrameOperator d
      (a.orthonormal (A.tubeHeightCoordinates ((collarHomeomorph A).symm q).val).1).val
  rw [cylinder_collar_coordinate_eq A p q he]

omit [IsManifold (𝓡 7) ∞ M] in
theorem handle_collar_frame_eq (p : handleOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) : pieceNormalFrame A .handle p = pieceNormalFrame A .collar q := by
  let z := unchangedHandleHomeomorph A p
  have hm := A.frame_eq_cylinder_collarCoordinates
    (ball_subset_closedBall z.property.1) (handle_collar_inner_lt A p q he).le
    (handleSuperlevel_vector_mem A z.val)
  change A.normalFrame z.val.val = _
  rw [hm]
  change boundaryFrameOperator d
    (a.orthonormal (A.collarCoordinates (unchangedHandleHomeomorph A p).val.val).1).val =
      boundaryFrameOperator d
        (a.orthonormal (A.tubeHeightCoordinates ((collarHomeomorph A).symm q).val).1).val
  rw [handle_collar_coordinate_eq A p q he]

omit [IsManifold (𝓡 7) ∞ M] in
theorem cylinder_handle_ne (p : cylinderOnlyPart A) (q : handleOnlyPart A) : p.val ≠ q.val := by
  intro he
  exact q.property (Or.inl ((congrArg Subtype.val he) ▸ cylinderOnlyPart_mem A p))

omit [IsManifold (𝓡 7) ∞ M] in
theorem pieceNormalFrame_agree (i j : Piece) (p : pieceDomain A i) (q : pieceDomain A j)
    (he : p.val = q.val) : pieceNormalFrame A i p = pieceNormalFrame A j q := by
  cases i with
  | cylinder =>
      cases j with
      | cylinder => exact congrArg (pieceNormalFrame A .cylinder) (Subtype.ext he)
      | handle => exact (cylinder_handle_ne A p q he).elim
      | collar => exact cylinder_collar_frame_eq A p q he
  | handle =>
      cases j with
      | cylinder => exact (cylinder_handle_ne A q p he.symm).elim
      | handle => exact congrArg (pieceNormalFrame A .handle) (Subtype.ext he)
      | collar => exact handle_collar_frame_eq A p q he
  | collar =>
      cases j with
      | cylinder => exact (cylinder_collar_frame_eq A q p he.symm).symm
      | handle => exact (handle_collar_frame_eq A q p he.symm).symm
      | collar => exact congrArg (pieceNormalFrame A .collar) (Subtype.ext he)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
